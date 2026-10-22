/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part15
import Books.ConvexAnalysis_Rockafellar_1970.convex_conjugate

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Corollary 6.28.8: a finite scalar constant can be pulled through the infimum over
any nonempty domain. -/
lemma helperForCorollary_6_28_8_finiteConstant_add_iInf
    {α : Type*} [Nonempty α] (c : ℝ) (F : α → EReal) :
    (⨅ x : α, (((c : ℝ) : EReal) + F x)) = (((c : ℝ) : EReal) + ⨅ x : α, F x) := by
  refine le_antisymm ?_ ?_
  · -- Approximate the right-hand infimum from above and compare to one slice of the left-hand side.
    refine
      (EReal.le_add_of_forall_gt (a := (((c : ℝ) : EReal))) (b := (⨅ x : α, F x))
        (c := (⨅ x : α, (((c : ℝ) : EReal) + F x))) ?_ ?_ ?_)
    · exact Or.inl (by simpa using (EReal.coe_ne_bot c))
    · exact Or.inl (by simp)
    · intro a ha b hb
      rcases (iInf_lt_iff.mp hb) with ⟨x, hx⟩
      exact le_trans
        (iInf_le (fun x : α => (((c : ℝ) : EReal) + F x)) x)
        (add_le_add ha.le hx.le)
  · -- Every lower approximation to `c + inf F` is bounded by each summand `c + F x`.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    refine le_iInf ?_
    intro x
    exact add_le_add ha.le (le_trans hb.le (iInf_le F x))

/-- Helper for Corollary 6.28.8: for `EReal`, negation commutes with a finite sum provided none
of the summands is `⊥`. -/
lemma helperForCorollary_6_28_8_neg_sum_of_ne_bot
    {n : ℕ} (f : Fin n → EReal) (hf : ∀ k : Fin n, f k ≠ ⊥) :
    (∑ k : Fin n, -f k) = -∑ k : Fin n, f k := by
  induction n with
  | zero =>
      -- The empty sum is stable under negation.
      simp
  | succ m ih =>
      -- Split off the first coordinate and use `EReal.neg_add` on the remaining finite sum.
      have hTailNeBot :
          ∑ k : Fin m, f k.succ ≠ (⊥ : EReal) :=
        finset_sum_ne_bot_of_forall (s := (Finset.univ : Finset (Fin m)))
          (f := fun k : Fin m => f k.succ) (fun k _ => hf k.succ)
      have hNegAdd :
          -(f 0 + ∑ k : Fin m, f k.succ) =
            -f 0 - ∑ k : Fin m, f k.succ := by
        exact EReal.neg_add (x := f 0) (y := ∑ k : Fin m, f k.succ)
          (Or.inl (hf 0)) (Or.inr hTailNeBot)
      calc
        ∑ k : Fin (m + 1), -f k
            = (-f 0) + ∑ k : Fin m, -f k.succ := by
                rw [Fin.sum_univ_succ]
        _ = (-f 0) + -∑ k : Fin m, f k.succ := by
              rw [ih (fun k : Fin m => f k.succ) (fun k : Fin m => hf k.succ)]
        _ = -(f 0 + ∑ k : Fin m, f k.succ) := by
              symm
              exact hNegAdd
        _ = -∑ k : Fin (m + 1), f k := by
              rw [Fin.sum_univ_succ]

/-- Helper for Corollary 6.28.8: after expanding the scalar Lagrangian, the primal infimum over
`Fin n → ℝ` should split into the sum of the one-dimensional coordinate infima. -/
theorem helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_add_sumInf
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    ∀ vStar : ℝ,
      unitSimplexSeparableDualFunction q vStar =
        ((-vStar : ℝ) : EReal) +
          ∑ k : Fin n,
            sInf (Set.range fun ξ : ℝ =>
              unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) +
                ((vStar * ξ : ℝ) : EReal)) := by
  intro vStar
  -- Expand the scalar Lagrangian and then pull the fixed `-vStar` term outside the primal infimum.
  unfold unitSimplexSeparableDualFunction
  rw [sInf_range]
  have hLagExpand :
      (⨅ x : Fin n → ℝ, unitSimplexSeparableLagrangian q vStar x) =
        ⨅ x : Fin n → ℝ,
          (((-vStar : ℝ) : EReal) +
            ∑ k : Fin n,
              (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
                ((vStar * x k : ℝ) : EReal))) := by
    apply iInf_congr
    intro x
    -- The affine-constraint family contributes exactly one `-vStar` shift.
    unfold unitSimplexSeparableLagrangian unitSimplexOrdinaryConvexReformulationData
    rw [Finset.sum_add_distrib]
    calc
      ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
          ∑ k : Fin n,
            (((vStar * unitSimplexCoordinateAffineConstraint k
              (fun _ : Fin 1 => x k) : ℝ) : EReal))
          = ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
              (((-vStar : ℝ) : EReal) +
                ∑ k : Fin n, ((vStar * x k : ℝ) : EReal)) := by
                rw [helperForCorollary_6_28_8_affineConstraintSum_eq_neg_vStar_add_coordinateSum
                  hn vStar x]
      _ = (((-vStar : ℝ) : EReal) +
            ((∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)) +
              ∑ k : Fin n, ((vStar * x k : ℝ) : EReal))) := by
              simp [add_assoc, add_left_comm, add_comm]
      _ = (((-vStar : ℝ) : EReal) +
            ∑ k : Fin n,
              (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
                ((vStar * x k : ℝ) : EReal))) := by
              rw [Finset.sum_add_distrib]
  rw [hLagExpand]
  rw [helperForCorollary_6_28_8_finiteConstant_add_iInf
    (-vStar) (fun x : Fin n → ℝ =>
      ∑ k : Fin n,
        (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
          ((vStar * x k : ℝ) : EReal)))]
  congr 1
  rw [helperForCorollary_6_28_8_tiltedCoordinate_iInf_eq_sum_iInf q vStar]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sInf_range]

/-- Helper for Corollary 6.28.8: once the product infimum is separated, the displayed dual
function formula with Fenchel conjugates follows by rewriting each coordinate infimum. -/
lemma helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_sub_sumFenchel
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    ∀ vStar : ℝ,
      unitSimplexSeparableDualFunction q vStar =
        ((-vStar : ℝ) : EReal) -
          ∑ k : Fin n,
            fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar) := by
  intro vStar
  -- Rewrite each coordinate infimum as the negative Fenchel conjugate.
  rw [helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_add_sumInf q hn vStar]
  have hCoordRewrite :
      ∑ k : Fin n,
          sInf (Set.range fun ξ : ℝ =>
            unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) +
              ((vStar * ξ : ℝ) : EReal)) =
        ∑ k : Fin n,
          -fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [helperForCorollary_6_28_8_coordinateInf_eq_neg_fenchelConjugate q k vStar]
  rw [hCoordRewrite]
  have hFenchelNeBot :
      ∀ k : Fin n,
        fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar) ≠
          (⊥ : EReal) := by
    intro k
    intro hBot
    let zeroVec : Fin 1 → ℝ := fun _ : Fin 1 => 0
    have hTermLe :
        (((zeroVec ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal) -
            unitSimplexCoordinateObjective q k zeroVec) ≤
          fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar) := by
      rw [fenchelConjugate_eq_iSup]
      exact le_iSup_of_le zeroVec le_rfl
    have hZeroNeTop : unitSimplexCoordinateObjective q k zeroVec ≠ (⊤ : EReal) := by
      have hZeroLtTop :
          unitSimplexCoordinateObjective q k zeroVec + (((0 : ℝ)) : EReal) < ⊤ := by
        simpa [zeroVec] using helperForCorollary_6_28_8_tiltedCoordinate_zero_lt_top q k 0
      intro hTop
      have : (⊤ : EReal) < ⊤ := by simpa [hTop] using hZeroLtTop
      exact lt_irrefl _ this
    have hZeroNeBot : unitSimplexCoordinateObjective q k zeroVec ≠ (⊥ : EReal) :=
      helperForCorollary_6_28_8_coordinateObjective_ne_bot q k zeroVec
    have hZeroSubNeBot :
        (((0 : ℝ) : EReal) - unitSimplexCoordinateObjective q k zeroVec) ≠ (⊥ : EReal) := by
      cases hObj : unitSimplexCoordinateObjective q k zeroVec <;> simp_all
    have hTermNeBot :
        (((zeroVec ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal) -
            unitSimplexCoordinateObjective q k zeroVec) ≠ (⊥ : EReal) := by
      calc
        (((zeroVec ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal) -
            unitSimplexCoordinateObjective q k zeroVec)
            = (((0 : ℝ) : EReal) - unitSimplexCoordinateObjective q k zeroVec) := by
                simp [zeroVec, dotProduct]
        _ ≠ (⊥ : EReal) := hZeroSubNeBot
    have hTermEqBot :
        (((zeroVec ⬝ᵥ (fun _ : Fin 1 => -vStar) : ℝ) : EReal) -
            unitSimplexCoordinateObjective q k zeroVec) = (⊥ : EReal) := by
      exact le_antisymm (by simpa [hBot] using hTermLe) bot_le
    exact hTermNeBot hTermEqBot
  rw [helperForCorollary_6_28_8_neg_sum_of_ne_bot
    (f := fun k : Fin n =>
      fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar))
    hFenchelNeBot]
  simp [sub_eq_add_neg]

/-- Helper for Corollary 6.28.8: the explicit penalty is the pointwise negative of the dual
function once the Fenchel-conjugate formula has been established. -/
lemma helperForCorollary_6_28_8_dualPenalty_eq_neg_dualFunction
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    ∀ vStar : ℝ,
      unitSimplexSeparableDualPenalty q vStar = - unitSimplexSeparableDualFunction q vStar := by
  intro vStar
  -- Substitute the explicit Fenchel-conjugate formula for the dual function and negate it.
  calc
    unitSimplexSeparableDualPenalty q vStar
        = (((vStar : ℝ) : EReal) +
            ∑ k : Fin n,
              fenchelConjugate 1 (unitSimplexCoordinateObjective q k)
                (fun _ : Fin 1 => -vStar)) := rfl
    _ = -((((-vStar : ℝ) : EReal) -
          ∑ k : Fin n,
            fenchelConjugate 1 (unitSimplexCoordinateObjective q k)
              (fun _ : Fin 1 => -vStar))) := by
            rw [sub_eq_add_neg]
            have hneg :
                -((((-vStar : ℝ) : EReal)) +
                    -(∑ k : Fin n,
                      fenchelConjugate 1 (unitSimplexCoordinateObjective q k)
                        (fun _ : Fin 1 => -vStar))) =
                  -((((-vStar : ℝ) : EReal)) : EReal) -
                    (-(∑ k : Fin n,
                      fenchelConjugate 1 (unitSimplexCoordinateObjective q k)
                        (fun _ : Fin 1 => -vStar))) := by
              exact EReal.neg_add (x := (((-vStar : ℝ) : EReal)))
                (y := -(∑ k : Fin n,
                  fenchelConjugate 1 (unitSimplexCoordinateObjective q k)
                    (fun _ : Fin 1 => -vStar)))
                (Or.inl (by simp)) (Or.inl (by simp))
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = - unitSimplexSeparableDualFunction q vStar := by
          rw [helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_sub_sumFenchel q hn vStar]

/-- Helper for Corollary 6.28.8: minimizing the explicit penalty is equivalent to maximizing the
dual function, because the penalty is pointwise `-g`. -/
theorem helperForCorollary_6_28_8_dualPenaltyMinimizer_iff_dualFunctionMaximizer
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    ∀ vStar : ℝ,
      IsUnitSimplexSeparableDualPenaltyMinimizer q vStar ↔
        unitSimplexSeparableDualFunction q vStar =
          sSup (Set.range fun wStar : ℝ => unitSimplexSeparableDualFunction q wStar) := by
  intro vStar
  constructor
  · intro hMin
    -- A penalty minimizer makes every competing dual value lie below `g(vStar)`.
    apply le_antisymm
    · exact le_sSup ⟨vStar, rfl⟩
    · refine sSup_le ?_
      rintro _ ⟨wStar, rfl⟩
      have hw := hMin wStar
      rw [helperForCorollary_6_28_8_dualPenalty_eq_neg_dualFunction q hn vStar,
        helperForCorollary_6_28_8_dualPenalty_eq_neg_dualFunction q hn wStar] at hw
      exact (EReal.neg_le_neg_iff.mp hw)
  · intro hSup
    -- Conversely, a dual maximizer minimizes the negated objective `-g`.
    intro wStar
    rw [helperForCorollary_6_28_8_dualPenalty_eq_neg_dualFunction q hn vStar,
      helperForCorollary_6_28_8_dualPenalty_eq_neg_dualFunction q hn wStar]
    refine (EReal.neg_le_neg_iff.mpr ?_)
    calc
      unitSimplexSeparableDualFunction q wStar
          ≤ sSup (Set.range fun uStar : ℝ => unitSimplexSeparableDualFunction q uStar) :=
            le_sSup ⟨wStar, rfl⟩
      _ = unitSimplexSeparableDualFunction q vStar := hSup.symm

/-- Helper for Corollary 6.28.8: Corollary 6.28.6 turns the scalar multiplier maximizers of the
dual function into Kuhn--Tucker vectors for the unit-simplex reformulation. -/
theorem helperForCorollary_6_28_8_isKuhnTuckerScalar_iff_dualFunctionMaximizer
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n)
    (h_exists : ∃ u : Fin 1 → ℝ, (unitSimplexSeparableOrdinaryConvexProgram q).IsKuhnTuckerVector u) :
    ∀ vStar : ℝ,
      ((unitSimplexSeparableOrdinaryConvexProgram q).IsKuhnTuckerVector fun _ : Fin 1 => vStar) ↔
        unitSimplexSeparableDualFunction q vStar =
          sSup (Set.range fun wStar : ℝ => unitSimplexSeparableDualFunction q wStar) := by
  intro vStar
  let P := unitSimplexSeparableOrdinaryConvexProgram q
  have hPrimalInfScalar :
      ∀ wStar : ℝ,
        P.lagrangianPrimalInf (fun _ : Fin 1 => wStar) = unitSimplexSeparableDualFunction q wStar := by
    intro wStar
    -- Rewrite the program Lagrangian pointwise to the scalarized separable Lagrangian.
    rw [BookOrdinaryConvexProgram.lagrangianPrimalInf, unitSimplexSeparableDualFunction]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact
        (helperForCorollary_6_28_8_programLagrangian_eq_unitSimplexSeparableLagrangian
          q hn wStar x).symm.trans hx
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact
        (helperForCorollary_6_28_8_programLagrangian_eq_unitSimplexSeparableLagrangian
          q hn wStar x).trans hx
  have hMaximinRewrite :
      P.lagrangianMaximin =
        sSup (Set.range fun wStar : ℝ => unitSimplexSeparableDualFunction q wStar) := by
    -- Collapse the `Fin 1 → ℝ` multiplier range to scalar multipliers.
    rw [BookOrdinaryConvexProgram.lagrangianMaximin]
    calc
      sSup (Set.range fun u : Fin 1 → ℝ => P.lagrangianPrimalInf u)
          = sSup (Set.range fun wStar : ℝ => P.lagrangianPrimalInf (fun _ : Fin 1 => wStar)) := by
              congr 1
              exact helperForCorollary_6_28_8_range_fin1_eq_range_scalar
                (Φ := fun u : Fin 1 → ℝ => P.lagrangianPrimalInf u)
      _ = sSup (Set.range fun wStar : ℝ => unitSimplexSeparableDualFunction q wStar) := by
            congr 1
            ext z
            constructor
            · rintro ⟨wStar, hw⟩
              exact ⟨wStar, (hPrimalInfScalar wStar).symm.trans hw⟩
            · rintro ⟨wStar, hw⟩
              exact ⟨wStar, (hPrimalInfScalar wStar).trans hw⟩
  -- Specialize Corollary 6.28.6 and rewrite the two extremal-value terms.
  calc
    P.IsKuhnTuckerVector (fun _ : Fin 1 => vStar)
        ↔ P.lagrangianPrimalInf (fun _ : Fin 1 => vStar) = P.lagrangianMaximin :=
          isKuhnTuckerVector_iff_lagrangianPrimalInf_eq_lagrangianMaximin_of_exists P h_exists
            (fun _ : Fin 1 => vStar)
    _ ↔ unitSimplexSeparableDualFunction q vStar =
          sSup (Set.range fun wStar : ℝ => unitSimplexSeparableDualFunction q wStar) := by
            rw [hPrimalInfScalar vStar, hMaximinRewrite]

/-- Corollary 6.28.8: Assume `0 < n` so that the simplex equation has a final coordinate carrying
the equality constraint. Then the scalar Lagrangian has the displayed separable formula, the dual
function is the constant `-vStar` plus the sum of scalar infima and also the corresponding
Fenchel-conjugate expression, and whenever a Kuhn--Tucker vector exists the scalar Kuhn--Tucker
vectors are exactly the minimizers of the explicit dual penalty. -/
theorem unitSimplexSeparable_lagrangian_dualFunction_and_dualMaximizer_formula
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (hn : 0 < n) :
    (∀ (vStar : ℝ) (x : Fin n → ℝ),
      unitSimplexSeparableLagrangian q vStar x =
        ((-vStar : ℝ) : EReal) +
          ∑ k : Fin n,
            (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
              ((vStar * x k : ℝ) : EReal))) ∧
      (∀ vStar : ℝ,
        unitSimplexSeparableDualFunction q vStar =
            ((-vStar : ℝ) : EReal) +
              ∑ k : Fin n,
                sInf (Set.range fun ξ : ℝ =>
                  unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) +
                    ((vStar * ξ : ℝ) : EReal)) ∧
          unitSimplexSeparableDualFunction q vStar =
            ((-vStar : ℝ) : EReal) -
              ∑ k : Fin n,
                fenchelConjugate 1 (unitSimplexCoordinateObjective q k) (fun _ : Fin 1 => -vStar)) ∧
      ((∃ u : Fin 1 → ℝ, (unitSimplexSeparableOrdinaryConvexProgram q).IsKuhnTuckerVector u) →
        ∀ vStar : ℝ,
          ((unitSimplexSeparableOrdinaryConvexProgram q).IsKuhnTuckerVector fun _ : Fin 1 => vStar) ↔
            IsUnitSimplexSeparableDualPenaltyMinimizer q vStar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vStar x
    -- Expand the scalar Lagrangian directly from the separable reformulation data.
    unfold unitSimplexSeparableLagrangian unitSimplexOrdinaryConvexReformulationData
    rw [Finset.sum_add_distrib]
    calc
      ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
          ∑ k : Fin n,
            (((vStar * unitSimplexCoordinateAffineConstraint k
              (fun _ : Fin 1 => x k) : ℝ) : EReal))
          = ∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
              (((-vStar : ℝ) : EReal) +
                ∑ k : Fin n, ((vStar * x k : ℝ) : EReal)) := by
                rw [helperForCorollary_6_28_8_affineConstraintSum_eq_neg_vStar_add_coordinateSum
                  hn vStar x]
      _ = (((-vStar : ℝ) : EReal) +
            ((∑ k : Fin n, unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k)) +
              ∑ k : Fin n, ((vStar * x k : ℝ) : EReal))) := by
              simp [add_assoc, add_left_comm, add_comm]
      _ = (((-vStar : ℝ) : EReal) +
            ∑ k : Fin n,
              (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
                ((vStar * x k : ℝ) : EReal))) := by
              rw [Finset.sum_add_distrib]
  · intro vStar
    -- Bundle the two displayed formulas for the dual function.
    exact ⟨helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_add_sumInf q hn vStar,
      helperForCorollary_6_28_8_dualFunction_eq_neg_vStar_sub_sumFenchel q hn vStar⟩
  · intro h_exists vStar
    -- Identify scalar Kuhn--Tucker vectors with minimizers of the explicit dual penalty.
    exact
      (helperForCorollary_6_28_8_isKuhnTuckerScalar_iff_dualFunctionMaximizer
        q hn h_exists vStar).trans
        (helperForCorollary_6_28_8_dualPenaltyMinimizer_iff_dualFunctionMaximizer
          q hn vStar).symm

/-- A block vector with block dimensions `n k`. -/
@[reducible] def DecompositionBlockVector : (s : ℕ) → (Fin s → ℕ) → Type :=
  fun s n => (k : Fin s) → Fin (n k) → ℝ

/-- The separable primal objective of a decomposition problem. -/
def decompositionPrimalObjective : {s : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        DecompositionBlockVector s n → ℝ :=
  fun {s} n f0 x => ∑ k, f0 k (x k)

/-- The equality-constraint value attached to a block vector in a decomposition problem. -/
def decompositionConstraintValue : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
        DecompositionBlockVector s n → Fin m → ℝ :=
  fun {s m} n A x i => ∑ k, (A k).mulVec (x k) i

/-- The `k`th coordinate objective obtained from the decomposition Lagrangian at a fixed
multiplier vector. -/
def decompositionCoordinateObjective : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (k : Fin s) → (Fin (n k) → ℝ) → ℝ :=
  fun {s m} n f0 A lambda k xk => f0 k xk + ∑ i, lambda i * (A k).mulVec xk i

/-- The set of minimizers of the coordinate objective `decompositionCoordinateObjective n f0 A
lambda k` attached to a decomposition problem. -/
def decompositionCoordinateMinimizerSet : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (k : Fin s) → Set (Fin (n k) → ℝ) :=
  fun {s m} n f0 A lambda k =>
    {xk |
      ∀ yk : Fin (n k) → ℝ,
        decompositionCoordinateObjective n f0 A lambda k xk ≤
          decompositionCoordinateObjective n f0 A lambda k yk}

/-- The Lagrangian of the separable equality-constrained decomposition problem. -/
def decompositionLagrangian : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → DecompositionBlockVector s n → ℝ :=
  fun {s m} n f0 A a lambda x =>
    decompositionPrimalObjective n f0 x +
      ∑ i, lambda i * (decompositionConstraintValue n A x i - a i)

/-- The extended primal objective equals the primal objective on feasible block vectors and `⊤`
otherwise. -/
noncomputable def decompositionExtendedPrimalObjective : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → DecompositionBlockVector s n → EReal :=
  fun {s m} n f0 A a x =>
    if decompositionConstraintValue n A x = a then
      (decompositionPrimalObjective n f0 x : EReal)
    else ⊤

/-- A multiplier vector is a decomposition Kuhn--Tucker vector when the dual value and the
extended primal infimum coincide at a common real value. -/
def IsDecompositionKuhnTuckerVector : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → Prop :=
  fun {s m} n f0 A a lambda =>
    ∃ v : ℝ,
      sInf (Set.range fun x => (decompositionLagrangian n f0 A a lambda x : EReal)) = (v : EReal) ∧
        sInf (Set.range fun x => decompositionExtendedPrimalObjective n f0 A a x) = (v : EReal)

/-- A decomposition-program Kuhn--Tucker vector is a Kuhn--Tucker vector for convex block
objectives. -/
def IsDecompositionOrdinaryConvexProgramKuhnTuckerVector : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → Prop :=
  fun {s m} n f0 A a lambda =>
    (∀ k : Fin s, ConvexOn ℝ Set.univ (f0 k)) ∧
      IsDecompositionKuhnTuckerVector n f0 A a lambda

/-- A block vector is optimal for the separable equality-constrained problem when it is feasible
and minimizes `decompositionPrimalObjective n f0` among all feasible block vectors. -/
def IsDecompositionOptimalSolution : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → DecompositionBlockVector s n → Prop :=
  fun {s m} n f0 A a x =>
    decompositionConstraintValue n A x = a ∧
      ∀ y : DecompositionBlockVector s n,
        decompositionConstraintValue n A y = a →
          decompositionPrimalObjective n f0 x ≤ decompositionPrimalObjective n f0 y

/-- Helper for Theorem 6.28.7: the separable Lagrangian splits into the constant term
`-⟪a, lambda⟫` plus the sum of coordinate objectives. -/
theorem helperForTheorem_6_28_7_lagrangian_eq_constant_add_sum_coordinateObjectives
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ) (x : DecompositionBlockVector s n) :
    decompositionLagrangian n f0 A a lambda x =
      -(dotProduct a lambda) + ∑ k, decompositionCoordinateObjective n f0 A lambda k (x k) := by
  -- Expand the Lagrangian and separate the fixed `-⟪a, lambda⟫` term from the blockwise terms.
  unfold decompositionLagrangian decompositionPrimalObjective decompositionConstraintValue
    decompositionCoordinateObjective
  have hConstraintPart :
      ∑ i : Fin m, lambda i * (∑ k : Fin s, (A k).mulVec (x k) i - a i) =
        (∑ i : Fin m, ∑ k : Fin s, lambda i * (A k).mulVec (x k) i) -
          ∑ i : Fin m, lambda i * a i := by
    calc
      ∑ i : Fin m, lambda i * (∑ k : Fin s, (A k).mulVec (x k) i - a i)
          = ∑ i : Fin m, ((∑ k : Fin s, lambda i * (A k).mulVec (x k) i) - lambda i * a i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_sub, Finset.mul_sum]
      _ =
          (∑ i : Fin m, ∑ k : Fin s, lambda i * (A k).mulVec (x k) i) -
            ∑ i : Fin m, lambda i * a i := by
              rw [Finset.sum_sub_distrib]
  calc
    (∑ k : Fin s, f0 k (x k)) +
        ∑ i : Fin m, lambda i * (∑ k : Fin s, (A k).mulVec (x k) i - a i)
      =
        (∑ k : Fin s, f0 k (x k)) +
          ((∑ i : Fin m, ∑ k : Fin s, lambda i * (A k).mulVec (x k) i) -
            ∑ i : Fin m, lambda i * a i) := by
              rw [hConstraintPart]
    _ =
        (∑ k : Fin s, f0 k (x k)) +
          ((∑ k : Fin s, ∑ i : Fin m, lambda i * (A k).mulVec (x k) i) -
            ∑ i : Fin m, lambda i * a i) := by
              rw [Finset.sum_comm]
    _ =
        -(∑ i : Fin m, a i * lambda i) +
          ((∑ k : Fin s, f0 k (x k)) +
            ∑ k : Fin s, ∑ i : Fin m, lambda i * (A k).mulVec (x k) i) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]
    _ =
        -(∑ i : Fin m, a i * lambda i) +
          ∑ k : Fin s, (f0 k (x k) + ∑ i : Fin m, lambda i * (A k).mulVec (x k) i) := by
              rw [← Finset.sum_add_distrib]
    _ =
        -(dotProduct a lambda) +
          ∑ k : Fin s, decompositionCoordinateObjective n f0 A lambda k (x k) := by
              simp [dotProduct, decompositionCoordinateObjective, mul_comm]

/-- Helper for Theorem 6.28.7: on a feasible block vector, the Lagrangian equals the primal
objective. -/
theorem helperForTheorem_6_28_7_lagrangian_eq_primalObjective_of_feasible
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ) {x : DecompositionBlockVector s n}
    (hx : decompositionConstraintValue n A x = a) :
    decompositionLagrangian n f0 A a lambda x = decompositionPrimalObjective n f0 x := by
  -- Feasibility makes every equality-constraint residual vanish.
  unfold decompositionLagrangian
  rw [hx]
  simp

/-- Helper for Theorem 6.28.7: an optimal feasible block vector minimizes the fixed-multiplier
Lagrangian. -/
theorem helperForTheorem_6_28_7_optimalSolution_minimizes_lagrangian
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ) {x : DecompositionBlockVector s n}
    (hx : IsDecompositionOptimalSolution n f0 A a x)
    (hKT : IsDecompositionKuhnTuckerVector n f0 A a lambda) :
    ∀ y : DecompositionBlockVector s n,
      decompositionLagrangian n f0 A a lambda x ≤ decompositionLagrangian n f0 A a lambda y := by
  rcases hx with ⟨hxFeas, hxOpt⟩
  rcases hKT with ⟨v, hvLag, hvPrimal⟩
  -- Optimality among feasible points shows that `x` minimizes the extended primal objective.
  have hxExtendedEq :
      decompositionExtendedPrimalObjective n f0 A a x = (v : EReal) := by
    apply le_antisymm
    · calc
        decompositionExtendedPrimalObjective n f0 A a x ≤
            sInf (Set.range fun z => decompositionExtendedPrimalObjective n f0 A a z) := by
              refine le_sInf ?_
              rintro _ ⟨z, rfl⟩
              by_cases hzFeas : decompositionConstraintValue n A z = a
              · -- On feasible competitors, primal optimality gives the comparison.
                simp [decompositionExtendedPrimalObjective, hxFeas, hzFeas]
                exact_mod_cast hxOpt z hzFeas
              · -- Infeasible competitors contribute `⊤`.
                simp [decompositionExtendedPrimalObjective, hxFeas, hzFeas]
        _ = (v : EReal) := hvPrimal
    · calc
        (v : EReal) =
            sInf (Set.range fun z => decompositionExtendedPrimalObjective n f0 A a z) :=
              hvPrimal.symm
        _ ≤ decompositionExtendedPrimalObjective n f0 A a x := by
              exact sInf_le ⟨x, rfl⟩
  -- The common Kuhn--Tucker value is also the Lagrangian value at the optimal feasible point.
  have hxLagEq :
      (decompositionLagrangian n f0 A a lambda x : EReal) = (v : EReal) := by
    calc
      (decompositionLagrangian n f0 A a lambda x : EReal) =
          (decompositionPrimalObjective n f0 x : EReal) := by
            exact_mod_cast
              helperForTheorem_6_28_7_lagrangian_eq_primalObjective_of_feasible
                n f0 A a lambda hxFeas
      _ = decompositionExtendedPrimalObjective n f0 A a x := by
            simp [decompositionExtendedPrimalObjective, hxFeas]
      _ = (v : EReal) := hxExtendedEq
  intro y
  -- Compare `L(x)` to the infimum of the Lagrangian range and then to `L(y)`.
  exact EReal.coe_le_coe_iff.mp <| by
    calc
      (decompositionLagrangian n f0 A a lambda x : EReal) = (v : EReal) := hxLagEq
      _ = sInf (Set.range fun z => (decompositionLagrangian n f0 A a lambda z : EReal)) :=
            hvLag.symm
      _ ≤ (decompositionLagrangian n f0 A a lambda y : EReal) := by
            exact sInf_le ⟨y, rfl⟩

/-- Helper for Theorem 6.28.7: a global minimizer of the separated Lagrangian must minimize each
coordinate objective. -/
theorem helperForTheorem_6_28_7_lagrangian_minimizer_gives_coordinatewise_minimizers
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ) {x : DecompositionBlockVector s n}
    (hmin :
      ∀ y : DecompositionBlockVector s n,
        decompositionLagrangian n f0 A a lambda x ≤ decompositionLagrangian n f0 A a lambda y) :
    ∀ k : Fin s, x k ∈ decompositionCoordinateMinimizerSet n f0 A lambda k := by
  intro k
  intro yk
  classical
  let g : Fin s → ℝ := fun j => decompositionCoordinateObjective n f0 A lambda j (x j)
  let y : DecompositionBlockVector s n := Function.update x k yk
  have hyMin :
      decompositionLagrangian n f0 A a lambda x ≤ decompositionLagrangian n f0 A a lambda y :=
    hmin y
  have hsumX :
      ∑ j : Fin s, decompositionCoordinateObjective n f0 A lambda j (x j) =
        g k + Finset.sum (Finset.univ.erase k) g := by
    -- Split the finite sum into the `k` summand plus the unchanged tail.
    simpa [g, add_comm] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s))) (a := k) (f := g)
        (Finset.mem_univ k)).symm
  have hfun :
      (fun j : Fin s => decompositionCoordinateObjective n f0 A lambda j (y j)) =
        Function.update g k (decompositionCoordinateObjective n f0 A lambda k yk) := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp [g, y]
    · simp [g, y, Function.update, hj]
  have hsumY :
      ∑ j : Fin s, decompositionCoordinateObjective n f0 A lambda j (y j) =
        decompositionCoordinateObjective n f0 A lambda k yk +
          Finset.sum (Finset.univ.erase k) g := by
    -- Only the `k`th summand changes under the block update.
    have hmem : k ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ k
    have hsdiff :
        (Finset.univ \ {k} : Finset (Fin s)) = (Finset.univ.erase k) := by
      simpa using (Finset.sdiff_singleton_eq_erase k (Finset.univ : Finset (Fin s)))
    calc
      ∑ j : Fin s, decompositionCoordinateObjective n f0 A lambda j (y j)
          = Finset.univ.sum (Function.update g k
              (decompositionCoordinateObjective n f0 A lambda k yk)) := by
                simp [hfun]
      _ =
          decompositionCoordinateObjective n f0 A lambda k yk +
            Finset.sum (Finset.univ.erase k) g := by
              simpa [hsdiff] using
                (Finset.sum_update_of_mem hmem (f := g)
                  (b := decompositionCoordinateObjective n f0 A lambda k yk))
  -- Rewrite both Lagrangians in separated form and cancel the unchanged summands.
  rw [helperForTheorem_6_28_7_lagrangian_eq_constant_add_sum_coordinateObjectives
        n f0 A a lambda x,
      helperForTheorem_6_28_7_lagrangian_eq_constant_add_sum_coordinateObjectives
        n f0 A a lambda y] at hyMin
  rw [hsumX, hsumY] at hyMin
  linarith

/-- Helper for Theorem 6.28.7: feasible block vectors whose coordinates minimize the separated
coordinate objectives are optimal. -/
theorem helperForTheorem_6_28_7_coordinatewise_minimizers_and_feasibility_imply_optimal
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ) {x : DecompositionBlockVector s n}
    (hxMin : ∀ k : Fin s, x k ∈ decompositionCoordinateMinimizerSet n f0 A lambda k)
    (hxFeas : decompositionConstraintValue n A x = a) :
    IsDecompositionOptimalSolution n f0 A a x := by
  refine ⟨hxFeas, ?_⟩
  intro y hyFeas
  -- Sum the coordinatewise minimizing inequalities over all blocks.
  have hCoordSum :
      ∑ k : Fin s, decompositionCoordinateObjective n f0 A lambda k (x k) ≤
        ∑ k : Fin s, decompositionCoordinateObjective n f0 A lambda k (y k) := by
    exact Finset.sum_le_sum (fun k hk => hxMin k (y k))
  have hLag :
      decompositionLagrangian n f0 A a lambda x ≤ decompositionLagrangian n f0 A a lambda y := by
    -- After separating the Lagrangian, both sides differ only by the summed coordinate terms.
    rw [helperForTheorem_6_28_7_lagrangian_eq_constant_add_sum_coordinateObjectives
          n f0 A a lambda x,
        helperForTheorem_6_28_7_lagrangian_eq_constant_add_sum_coordinateObjectives
          n f0 A a lambda y]
    linarith
  -- Feasibility turns the Lagrangian comparison back into primal optimality.
  calc
    decompositionPrimalObjective n f0 x = decompositionLagrangian n f0 A a lambda x :=
      (helperForTheorem_6_28_7_lagrangian_eq_primalObjective_of_feasible
        n f0 A a lambda hxFeas).symm
    _ ≤ decompositionLagrangian n f0 A a lambda y := hLag
    _ = decompositionPrimalObjective n f0 y :=
      helperForTheorem_6_28_7_lagrangian_eq_primalObjective_of_feasible
        n f0 A a lambda hyFeas

/-- Theorem 6.28.7: Let `f₀ₖ` be the block objectives and `Aₖ` the block matrices of a
decomposition problem. Then the optimal solutions of the original problem are exactly the feasible
block vectors whose coordinates minimize the corresponding coordinate objectives. -/
theorem decompositionOptimalSolutionSet_eq_coordinateMinimizerSet
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a lambda : Fin m → ℝ)
    (hsetup : IsDecompositionOrdinaryConvexProgramKuhnTuckerVector n f0 A a lambda) :
    {x | IsDecompositionOptimalSolution n f0 A a x} =
      {x |
        (∀ k : Fin s, x k ∈ decompositionCoordinateMinimizerSet n f0 A lambda k) ∧
          decompositionConstraintValue n A x = a} := by
  ext x
  constructor
  · intro hx
    rcases hsetup with ⟨_hconvex, hKT⟩
    have hxFeas : decompositionConstraintValue n A x = a := hx.1
    -- Optimal solutions globally minimize the fixed-multiplier Lagrangian.
    have hLagMin :
        ∀ y : DecompositionBlockVector s n,
          decompositionLagrangian n f0 A a lambda x ≤ decompositionLagrangian n f0 A a lambda y :=
      helperForTheorem_6_28_7_optimalSolution_minimizes_lagrangian n f0 A a lambda hx hKT
    -- Varying one block at a time forces each block to minimize its separated coordinate term.
    exact ⟨helperForTheorem_6_28_7_lagrangian_minimizer_gives_coordinatewise_minimizers
      n f0 A a lambda hLagMin, hxFeas⟩
  · rintro ⟨hxMin, hxFeas⟩
    -- The converse is the additive textbook argument: sum the blockwise inequalities and use
    -- feasibility to recover the primal objective.
    exact
      helperForTheorem_6_28_7_coordinatewise_minimizers_and_feasibility_imply_optimal
        n f0 A a lambda hxMin hxFeas

/-- The dual function of the separable decomposition problem. -/
noncomputable def decompositionDualFunction : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → EReal :=
  fun {s m} n f0 A a uStar =>
    sInf (Set.range fun x => (decompositionLagrangian n f0 A a uStar x : EReal))

/-- The explicit dual penalty `w = -g` for the decomposition problem. -/
noncomputable def decompositionDualPenalty : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → EReal :=
  fun {s m} n f0 A a uStar =>
    ((dotProduct a uStar : ℝ) : EReal) +
      ∑ k : Fin s,
        convexConjugate (fun xk => (f0 k xk : EReal))
          (fun j => -((A k).transpose.mulVec uStar j))

/-- A minimizer of the explicit decomposition dual penalty. -/
def IsDecompositionDualPenaltyMinimizer : {s m : ℕ} →
    (n : Fin s → ℕ) →
      ((k : Fin s) → (Fin (n k) → ℝ) → ℝ) →
        ((k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ) →
          (Fin m → ℝ) → (Fin m → ℝ) → Prop :=
  fun {s m} n f0 A a uStar =>
    ∀ vStar : Fin m → ℝ,
      decompositionDualPenalty n f0 A a uStar ≤ decompositionDualPenalty n f0 A a vStar

/-- Helper for Theorem 6.28.8: assemble a block vector in `Fin (m + 1)` from its `Fin.castSucc`
tail together with its last block. -/
def helperForTheorem_6_28_8_lastCasesBlockVector : {m : ℕ} →
    (n : Fin (m + 1) → ℕ) →
      (DecompositionBlockVector m fun k => n (Fin.castSucc k)) →
        (Fin (n (Fin.last m)) → ℝ) → DecompositionBlockVector (m + 1) n :=
  fun {m} n y ξ i => Fin.lastCases (motive := fun i => Fin (n i) → ℝ) ξ (fun k => y k) i

/-- Helper for Theorem 6.28.8: after Theorem 6.28.7 separates the Lagrangian into coordinate
objectives, each block-affine term can be rewritten as a dot product against `Aₖᵀ uStar`. -/
theorem helperForTheorem_6_28_8_lagrangian_eq_neg_dotProduct_add_sum_blockDotProducts
    {s m : ℕ} (n : Fin s → ℕ)
    (f0 : (k : Fin s) → (Fin (n k) → ℝ) → ℝ)
    (A : (k : Fin s) → Matrix (Fin m) (Fin (n k)) ℝ)
    (a uStar : Fin m → ℝ) (x : DecompositionBlockVector s n) :
    decompositionLagrangian n f0 A a uStar x =
      -(dotProduct a uStar) +
        ∑ k : Fin s, (f0 k (x k) + dotProduct (x k) ((A k).transpose.mulVec uStar)) := by
  unfold decompositionLagrangian decompositionPrimalObjective decompositionConstraintValue
  calc
    (∑ k : Fin s, f0 k (x k)) +
          ∑ i : Fin m, uStar i * ((∑ k : Fin s, (A k).mulVec (x k) i) - a i)
        = (∑ k : Fin s, f0 k (x k)) +
            (((fun i : Fin m => ∑ k : Fin s, (A k).mulVec (x k) i) ⬝ᵥ uStar) -
              a ⬝ᵥ uStar) := by
                congr 1
                simp [dotProduct, mul_sub, Finset.sum_sub_distrib, mul_comm]
    _ = (∑ k : Fin s, f0 k (x k)) +
          ((∑ k : Fin s, (A k).mulVec (x k) ⬝ᵥ uStar) - a ⬝ᵥ uStar) := by
            congr 2
            rw [dotProduct]
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            simp [dotProduct]
    _ = (∑ k : Fin s, f0 k (x k)) +
          ((∑ k : Fin s, x k ⬝ᵥ (A k).transpose.mulVec uStar) - a ⬝ᵥ uStar) := by
            apply congrArg (fun z : ℝ => (∑ k : Fin s, f0 k (x k)) + (z - a ⬝ᵥ uStar))
            apply Finset.sum_congr rfl
            intro k _
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = -(a ⬝ᵥ uStar) +
          ∑ k : Fin s, (f0 k (x k) + x k ⬝ᵥ (A k).transpose.mulVec uStar) := by
            rw [Finset.sum_add_distrib]
            ring

/-- Helper for Theorem 6.28.8: a dependent block vector indexed by `Fin (m + 1)` can be split
into its `Fin.castSucc` tail together with its last block. -/
theorem helperForTheorem_6_28_8_blockVector_iInf_lastCases
    {m : ℕ} (n : Fin (m + 1) → ℕ)
    (F : DecompositionBlockVector (m + 1) n → EReal) :
    (⨅ x, F x) =
      ⨅ y : DecompositionBlockVector m (fun k => n (Fin.castSucc k)),
        ⨅ ξ : Fin (n (Fin.last m)) → ℝ,
          F (helperForTheorem_6_28_8_lastCasesBlockVector n y ξ) := by
  apply le_antisymm
  · refine le_iInf ?_
    intro y
    refine le_iInf ?_
    intro ξ
    exact iInf_le F (helperForTheorem_6_28_8_lastCasesBlockVector n y ξ)
  · refine le_iInf ?_
    intro x
    let y : DecompositionBlockVector m (fun k => n (Fin.castSucc k)) :=
      fun k => x (Fin.castSucc k)
    let ξ : Fin (n (Fin.last m)) → ℝ := x (Fin.last m)
    have hReconstruct : helperForTheorem_6_28_8_lastCasesBlockVector n y ξ = x := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [helperForTheorem_6_28_8_lastCasesBlockVector, ξ]
      · simp [helperForTheorem_6_28_8_lastCasesBlockVector, y]
    exact le_trans (iInf_le_of_le y (iInf_le _ ξ)) (by simpa [hReconstruct])

end Section28
end Chap06
