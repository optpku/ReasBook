/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part24

open scoped BigOperators Pointwise

section Chap06
section Section30

/-- Helper for Theorem 6.30.24: multiplying a finite `EReal` value shifted by a real constant by
another real scalar can be normalized entirely inside `ℝ`. -/
lemma helperForTheorem_6_30_24_finiteScalarMul_add_realConst
    {lam c : ℝ} {a : EReal}
    (ha_bot : a ≠ (⊥ : EReal)) (ha_top : a < (⊤ : EReal)) :
    (((lam : ℝ) : EReal) * (a + ((c : ℝ) : EReal))) =
      ((((lam : ℝ) : EReal) * a) + (((lam * c : ℝ) : EReal))) := by
  have hcoe : (((a.toReal : ℝ)) : EReal) = a := by
    exact EReal.coe_toReal (x := a) ((lt_top_iff_ne_top).1 ha_top) ha_bot
  -- Once the finite value is rewritten via `toReal`, the claim is just real distributivity.
  rw [← hcoe]
  change ((((lam * (a.toReal + c) : ℝ)) : ℝ) : EReal) =
    ((((lam * a.toReal + lam * c : ℝ)) : ℝ) : EReal)
  simp [mul_add]

/-- Helper for Theorem 6.30.24: for a fixed constraint index `i`, minimizing over the mixed block
`(vᵢ, pᵢ)` first removes the scalar threshold and then collapses the translated affine block to
the displayed linear term plus the corresponding summand of the explicit dual objective. -/
lemma helperForTheorem_6_30_24_constraintBlock_iInf_eq_weighted_linear_minus_scaledFenchel
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ)
    (x : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (i : Fin m) (hnonneg_i : 0 ≤ wStar.vStar i) :
    (⨅ q : ℝ × (Fin (ni i) → ℝ),
        (if data.h i ((data.A i).mulVec x + data.a i - q.2) +
              ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
            ((q.1 : ℝ) : EReal) then
            (0 : EReal)
          else
            (⊤ : EReal)) +
          (((q.1 * wStar.vStar i : ℝ) : EReal)) +
          (((q.2 ⬝ᵥ wStar.p i : ℝ) : EReal))) =
      (((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) : ℝ) :
          EReal)) +
        ((((data.α i * wStar.vStar i : ℝ) : EReal) +
              ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
          fenchelConjugate (ni i)
            (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
            (wStar.p i)) := by
  let c : ℝ := (data.aStar i ⬝ᵥ x : ℝ) + data.α i
  let g : (Fin (ni i) → ℝ) → EReal := fun y => data.h i y + ((c : ℝ) : EReal)
  have hg_bot : ∀ y : Fin (ni i) → ℝ, g y ≠ (⊥ : EReal) := by
    intro y
    have hcoe : (((data.h i y).toReal : ℝ) : EReal) = data.h i y := by
      exact EReal.coe_toReal (x := data.h i y)
        ((lt_top_iff_ne_top).1
          (helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
            (data := data) (i := i) (y := y) (hdomi := hdom i)))
        ((hh i).1.1.1 y)
    have hgEq : g y = ((((data.h i y).toReal + c : ℝ)) : EReal) := by
      calc
        g y = (((data.h i y).toReal : ℝ) : EReal) + ((c : ℝ) : EReal) := by
          simpa [g] using congrArg (fun t : EReal => t + ((c : ℝ) : EReal)) hcoe.symm
        _ = ((((data.h i y).toReal + c : ℝ)) : EReal) := by simp [EReal.coe_add]
    rw [hgEq]
    exact EReal.coe_ne_bot _
  have hg_top : ∀ y : Fin (ni i) → ℝ, g y < (⊤ : EReal) := by
    intro y
    exact EReal.add_lt_top
      (ne_of_lt (helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
        (data := data) (i := i) (y := y) (hdomi := hdom i)))
      (EReal.coe_ne_top _)
  have hscaled_split :
      (⨅ y : Fin (ni i) → ℝ,
          ((((wStar.vStar i : ℝ) : EReal) * g ((data.A i).mulVec x + data.a i - y)) +
            (((y ⬝ᵥ wStar.p i : ℝ) : EReal)))) =
        (⨅ y : Fin (ni i) → ℝ,
          ((((wStar.vStar i : ℝ) : EReal) *
                data.h i ((data.A i).mulVec x + data.a i - y)) +
              (((y ⬝ᵥ wStar.p i : ℝ) : EReal))) +
            (((wStar.vStar i * c : ℝ) : EReal))) := by
    refine iInf_congr ?_
    intro y
    have hscale :
        (((wStar.vStar i : ℝ) : EReal) *
            (data.h i ((data.A i).mulVec x + data.a i - y) + ((c : ℝ) : EReal))) =
          ((((wStar.vStar i : ℝ) : EReal) * data.h i ((data.A i).mulVec x + data.a i - y)) +
            (((wStar.vStar i * c : ℝ) : EReal))) := by
      exact helperForTheorem_6_30_24_finiteScalarMul_add_realConst
        (lam := wStar.vStar i) (c := c)
        ((hh i).1.1.1 ((data.A i).mulVec x + data.a i - y))
        (helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
          (data := data) (i := i) (y := (data.A i).mulVec x + data.a i - y)
          (hdomi := hdom i))
    -- Normalize the shifted scaled block so the weighted constant becomes an explicit addend.
    calc
      ((((wStar.vStar i : ℝ) : EReal) * g ((data.A i).mulVec x + data.a i - y)) +
            (((y ⬝ᵥ wStar.p i : ℝ) : EReal))) =
          ((((wStar.vStar i : ℝ) : EReal) *
                (data.h i ((data.A i).mulVec x + data.a i - y) + ((c : ℝ) : EReal))) +
              (((y ⬝ᵥ wStar.p i : ℝ) : EReal))) := by
                simp [g]
      _ =
          (((((wStar.vStar i : ℝ) : EReal) * data.h i ((data.A i).mulVec x + data.a i - y)) +
                (((wStar.vStar i * c : ℝ) : EReal))) +
              (((y ⬝ᵥ wStar.p i : ℝ) : EReal))) := by
                rw [hscale]
      _ =
          (((((wStar.vStar i : ℝ) : EReal) * data.h i ((data.A i).mulVec x + data.a i - y)) +
                (((y ⬝ᵥ wStar.p i : ℝ) : EReal))) +
              (((wStar.vStar i * c : ℝ) : EReal))) := by
                simp [add_left_comm, add_comm]
  have hAffine :
      ((((data.A i).mulVec x + data.a i) ⬝ᵥ wStar.p i : ℝ) + (wStar.vStar i * c)) =
        (x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) : ℝ) +
          (data.α i * wStar.vStar i + (data.a i ⬝ᵥ wStar.p i : ℝ)) := by
    -- The remaining real affine terms are exactly the indexed collection identity.
    simpa [c, mul_add, add_assoc, add_left_comm, add_comm] using
      helperForTheorem_6_30_24_constraintAffineTerms_collect data i x (wStar.vStar i)
        (wStar.p i)
  -- First eliminate the scalar threshold, then pull out the weighted finite constant and collapse
  -- the translated affine block for the scaled function.
  rw [helperForTheorem_6_30_22_constraintPair_iInf_eq_weightedTranslated
    (g := g) (x := (data.A i).mulVec x + data.a i) (p := wStar.p i)
    (lam := wStar.vStar i) (hlam := hnonneg_i) (hg_bot := hg_bot) (hg_top := hg_top)]
  rw [hscaled_split, helperForTheorem_6_30_22_iInf_add_realConst
    (G := fun y : Fin (ni i) → ℝ =>
      ((((wStar.vStar i : ℝ) : EReal) * data.h i ((data.A i).mulVec x + data.a i - y)) +
        (((y ⬝ᵥ wStar.p i : ℝ) : EReal))))
    (c := wStar.vStar i * c)]
  rw [helperForTheorem_6_30_22_translatedAffineBlock_iInf_eq_linear_minus_fenchel
    (g := fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
    (x := (data.A i).mulVec x + data.a i) (p := wStar.p i)]
  rw [sub_eq_add_neg]
  calc
    ((((data.A i).mulVec x + data.a i) ⬝ᵥ wStar.p i : ℝ) : EReal) +
          -fenchelConjugate (ni i)
            (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
            (wStar.p i) +
        (((wStar.vStar i * c : ℝ) : EReal)) =
      (((((((data.A i).mulVec x + data.a i) ⬝ᵥ wStar.p i : ℝ) + (wStar.vStar i * c) : ℝ)) :
            ℝ) : EReal) +
        -fenchelConjugate (ni i)
          (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
          (wStar.p i) := by
            simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
    _ =
      (((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
            ℝ) : EReal)) +
        ((((data.α i * wStar.vStar i : ℝ) : EReal) +
              ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) +
          -fenchelConjugate (ni i)
            (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
            (wStar.p i)) := by
            simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using
              congrArg
                (fun t : ℝ =>
                  ((t : ℝ) : EReal) +
                    -fenchelConjugate (ni i)
                      (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                      (wStar.p i))
                hAffine
    _ =
      (((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
            ℝ) : EReal)) +
        ((((data.α i * wStar.vStar i : ℝ) : EReal) +
              ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
          fenchelConjugate (ni i)
            (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
            (wStar.p i)) := by
            rw [sub_eq_add_neg]

/-- Helper for Theorem 6.30.24: the nested infimum over the scalar thresholds and dependent
translation family can be reindexed as a single dependent family of coordinate pairs. -/
lemma helperForTheorem_6_30_24_tailBlock_nested_iInf_to_dependentFamilyPairs_staged
    {m : ℕ} {β : Fin m → Type*}
    (H : ∀ i : Fin m, ℝ → β i → EReal) :
    (⨅ v : Fin m → ℝ, ⨅ p : ∀ i : Fin m, β i,
        ∑ i : Fin m, H i (v i) (p i)) =
      (⨅ z : ∀ i : Fin m, ℝ × β i,
        ∑ i : Fin m, H i (z i).1 (z i).2) := by
  calc
    (⨅ v : Fin m → ℝ, ⨅ p : ∀ i : Fin m, β i,
        ∑ i : Fin m, H i (v i) (p i)) =
      (⨅ q : (Fin m → ℝ) × ((i : Fin m) → β i),
        ∑ i : Fin m, H i (q.1 i) (q.2 i)) := by
          simpa using
            (helperForTheorem_6_30_22_iInf_prod_eq_nested
              (H := fun v : Fin m → ℝ => fun p : ∀ i : Fin m, β i =>
                ∑ i : Fin m, H i (v i) (p i))).symm
    _ =
      (⨅ z : ∀ i : Fin m, ℝ × β i,
        ∑ i : Fin m, H i (z i).1 (z i).2) := by
          refine le_antisymm ?_ ?_
          · refine le_iInf ?_
            intro z
            exact le_trans
              (iInf_le
                (fun q : (Fin m → ℝ) × ((i : Fin m) → β i) =>
                  ∑ i : Fin m, H i (q.1 i) (q.2 i))
                (fun i => (z i).1, fun i => (z i).2))
              (by simp)
          · refine le_iInf ?_
            intro q
            exact le_trans
              (iInf_le
                (fun z : ∀ i : Fin m, ℝ × β i =>
                  ∑ i : Fin m, H i (z i).1 (z i).2)
                (fun i => (q.1 i, q.2 i)))
              (by simp)

/-- Helper for Theorem 6.30.24: after fixing the primal point `x`, the infimum over the indexed
constraint thresholds and translations packages into the finite sum of the blockwise constraint
formulas. -/
lemma helperForTheorem_6_30_24_tailBlock_iInf_eq_sum_constraintBlocks
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ)
    (x : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.vStar i) :
    (⨅ v : Fin m → ℝ,
        ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          indicatorFunction (intermediateProgramFeasibleSet data
              ({ v := v, p0 := (0 : Fin n0 → ℝ), p := p } :
                IntermediateProgramParameter m n n0 ni)) x +
            (((v ⬝ᵥ wStar.vStar : ℝ) : EReal)) +
            ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal))) =
      ∑ i : Fin m,
        ((((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
              ℝ) : EReal)) +
          ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
            fenchelConjugate (ni i)
              (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
              (wStar.p i))) := by
  let block : ∀ i : Fin m, ℝ → (Fin (ni i) → ℝ) → EReal := fun i v p =>
    (if data.h i ((data.A i).mulVec x + data.a i - p) +
          ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
        ((v : ℝ) : EReal) then
      (0 : EReal)
    else
      (⊤ : EReal)) +
      (((v * wStar.vStar i : ℝ) : EReal)) +
      (((p ⬝ᵥ wStar.p i : ℝ) : EReal))
  have hfinite_block :
      ∀ i : Fin m, ∃ q : ℝ × (Fin (ni i) → ℝ), block i q.1 q.2 < (⊤ : EReal) := by
    intro i
    let c : ℝ := (data.aStar i ⬝ᵥ x : ℝ) + data.α i
    have hvalue_top :
        data.h i ((data.A i).mulVec x + data.a i) < (⊤ : EReal) := by
      exact helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
        (data := data) (i := i) (y := (data.A i).mulVec x + data.a i) (hdomi := hdom i)
    have hterm_ne_top :
        data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal) ≠ (⊤ : EReal) :=
      EReal.add_ne_top (ne_of_lt hvalue_top) (EReal.coe_ne_top _)
    refine ⟨(((data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal)).toReal),
        (0 : Fin (ni i) → ℝ)), ?_⟩
    have hle :
        data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal) ≤
          ((((data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal)).toReal : ℝ)) :
            EReal) := by
      simpa using
        EReal.le_coe_toReal
          (x := data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal))
          hterm_ne_top
    have hblock :
        block i (data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal)).toReal
            (0 : Fin (ni i) → ℝ) =
          ((((data.h i ((data.A i).mulVec x + data.a i) + ((c : ℝ) : EReal)).toReal *
              wStar.vStar i : ℝ) : EReal)) := by
      have hcoec :
          (((c : ℝ) : EReal)) =
            (((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal)) := by
        simp [c, EReal.coe_add]
      have hle' :
          data.h i ((data.A i).mulVec x + data.a i) +
              ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal))) ≤
            ((((data.h i ((data.A i).mulVec x + data.a i) +
                  ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal)))).toReal :
                  ℝ)) :
              EReal) := by
        simpa [hcoec, add_assoc] using hle
      have hif :
          (if data.h i ((data.A i).mulVec x + data.a i) +
                ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal))) ≤
              ((((data.h i ((data.A i).mulVec x + data.a i) +
                    ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal)))).toReal :
                    ℝ)) :
                EReal) then
              (0 : EReal)
            else
              (⊤ : EReal)) = 0 := by
        simp [hle']
      simp [block, c, hcoec, hif, add_assoc]
    rw [hblock]
    exact (lt_top_iff_ne_top).2 (EReal.coe_ne_top _)
  -- Normalize the tail integrand into coordinate blocks, then split the dependent family infimum
  -- into the sum of the individual block infima.
  calc
    (⨅ v : Fin m → ℝ,
        ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          indicatorFunction (intermediateProgramFeasibleSet data
              ({ v := v, p0 := (0 : Fin n0 → ℝ), p := p } :
                IntermediateProgramParameter m n n0 ni)) x +
            (((v ⬝ᵥ wStar.vStar : ℝ) : EReal)) +
            ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal))) =
      (⨅ v : Fin m → ℝ,
        ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          ∑ i : Fin m, block i (v i) (p i)) := by
            refine iInf_congr ?_
            intro v
            refine iInf_congr ?_
            intro p
            calc
              indicatorFunction (intermediateProgramFeasibleSet data
                    ({ v := v, p0 := (0 : Fin n0 → ℝ), p := p } :
                      IntermediateProgramParameter m n n0 ni)) x +
                  (((v ⬝ᵥ wStar.vStar : ℝ) : EReal)) +
                  ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal)) =
                (∑ i : Fin m,
                    (if data.h i ((data.A i).mulVec x + data.a i - p i) +
                          ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
                        ((v i : ℝ) : EReal) then
                        (0 : EReal)
                      else
                        (⊤ : EReal))) +
                  ((((∑ i : Fin m, v i * wStar.vStar i : ℝ)) : ℝ) : EReal) +
                  ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal)) := by
                    rw [helperForTheorem_6_30_24_feasibleIndicator_eq_sum_pairIndicators
                      (data := data) (x := x) (v := v) (p0 := (0 : Fin n0 → ℝ)) (p := p)]
                    simp [dotProduct]
              _ =
                (∑ i : Fin m,
                    (if data.h i ((data.A i).mulVec x + data.a i - p i) +
                          ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
                        ((v i : ℝ) : EReal) then
                        (0 : EReal)
                      else
                        (⊤ : EReal))) +
                  ∑ i : Fin m, (((v i * wStar.vStar i : ℝ) : EReal)) +
                  ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal)) := by
                    rw [helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe]
              _ =
                (∑ i : Fin m,
                    ((if data.h i ((data.A i).mulVec x + data.a i - p i) +
                          ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
                        ((v i : ℝ) : EReal) then
                        (0 : EReal)
                      else
                        (⊤ : EReal)) +
                      (((v i * wStar.vStar i : ℝ) : EReal)))) +
                  ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal)) := by
                    rw [← Finset.sum_add_distrib]
              _ =
                ∑ i : Fin m,
                  (((if data.h i ((data.A i).mulVec x + data.a i - p i) +
                        ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
                      ((v i : ℝ) : EReal) then
                      (0 : EReal)
                    else
                      (⊤ : EReal)) +
                    (((v i * wStar.vStar i : ℝ) : EReal))) +
                    (((p i ⬝ᵥ wStar.p i : ℝ) : EReal))) := by
                      rw [← Finset.sum_add_distrib]
              _ =
                ∑ i : Fin m, block i (v i) (p i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simp [block, add_assoc]
    _ =
      (⨅ z : ∀ i : Fin m, ℝ × (Fin (ni i) → ℝ),
          ∑ i : Fin m, block i (z i).1 (z i).2) := by
            simpa [block] using
              helperForTheorem_6_30_24_tailBlock_nested_iInf_to_dependentFamilyPairs_staged
                (H := block)
    _ =
      ∑ i : Fin m, (⨅ q : ℝ × (Fin (ni i) → ℝ), block i q.1 q.2) := by
            let gPair : ∀ i : Fin m, (ℝ × (Fin (ni i) → ℝ)) → EReal := fun i q =>
              block i q.1 q.2
            have hgPair :
                (⨅ z : ∀ i : Fin m, ℝ × (Fin (ni i) → ℝ),
                    ∑ i : Fin m, block i (z i).1 (z i).2) =
                  (⨅ z : ∀ i : Fin m, ℝ × (Fin (ni i) → ℝ),
                    ∑ i : Fin m, gPair i (z i)) := by
              simp [gPair]
            rw [hgPair]
            simpa [gPair] using
              helperForTheorem_6_30_24_dependentFamily_iInf_sum_eq_sum_iInf_generic
                (g := gPair) (hfinite := hfinite_block)
    _ =
      ∑ i : Fin m,
        ((((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
              ℝ) : EReal)) +
          ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
            fenchelConjugate (ni i)
              (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
              (wStar.p i))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [block] using
              helperForTheorem_6_30_24_constraintBlock_iInf_eq_weighted_linear_minus_scaledFenchel
                (data := data) (hh := hh) (hdom := hdom) (x := x) (wStar := wStar)
                (i := i) (hnonneg_i := hnonneg i)

/-- Helper for Theorem 6.30.24: after fixing the primal point `x`, the infimum over the
heterogeneous perturbation parameter `w = (v, p₀, p)` collapses to the free linear term with
coefficient `a₀* + ∑ᵢ vᵢ* aᵢ* + A₀ᵀ p₀* + ∑ᵢ Aᵢᵀ pᵢ* - x*` plus the explicit dual objective. -/
lemma helperForTheorem_6_30_24_fixedX_parameterInf_eq_linearPlusDualObjective
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ) :
    ∀ x : Fin n → ℝ, ∀ xStar : Fin n → ℝ,
      ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
        (∀ i : Fin m, 0 ≤ wStar.vStar i) →
          (⨅ w : IntermediateProgramParameter m n n0 ni,
              intermediateProgramBifunction data w x -
                (((x ⬝ᵥ xStar : ℝ) : EReal)) +
                (((intermediateProgramDualPairing w wStar : ℝ) : EReal))) =
            (((x ⬝ᵥ
                (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) :
                EReal)) +
              intermediateProgramDualObjective data wStar := by
  intro x xStar wStar hnonneg
  let p0Block : (Fin n0 → ℝ) → EReal := fun p0 =>
    data.h0 (data.A0.mulVec x + data.a0 - p0) +
      ((((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal)) +
      (((p0 ⬝ᵥ wStar.p0 : ℝ) : EReal))
  let tailBlock : (Fin m → ℝ) → (∀ i : Fin m, Fin (ni i) → ℝ) → EReal := fun v p =>
    indicatorFunction (intermediateProgramFeasibleSet data
        ({ v := v, p0 := (0 : Fin n0 → ℝ), p := p } :
          IntermediateProgramParameter m n n0 ni)) x +
      (((v ⬝ᵥ wStar.vStar : ℝ) : EReal)) +
      ∑ i : Fin m, (((p i ⬝ᵥ wStar.p i : ℝ) : EReal))
  let tailBlockProd :
      ((Fin m → ℝ) × (∀ i : Fin m, Fin (ni i) → ℝ)) → EReal := fun q =>
    tailBlock q.1 q.2
  have hfinite_p0 : ∃ p0 : Fin n0 → ℝ, p0Block p0 < (⊤ : EReal) := by
    rcases hh0.1.1.2 with ⟨y0, hy0_ne_top⟩
    refine ⟨data.A0.mulVec x + data.a0 - y0, ?_⟩
    have hy0_top : data.h0 y0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hy0_ne_top
    have hsum1 :
        data.h0 y0 + ((((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal)) < (⊤ : EReal) := by
      exact EReal.add_lt_top (ne_of_lt hy0_top) (EReal.coe_ne_top _)
    have hsum2 :
        data.h0 y0 + ((((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal)) +
            ((((data.A0.mulVec x + data.a0 - y0) ⬝ᵥ wStar.p0 : ℝ) : EReal)) < (⊤ : EReal) := by
      exact EReal.add_lt_top (ne_of_lt hsum1) (EReal.coe_ne_top _)
    -- Choosing `p₀ = A₀x + a₀ - y₀` turns the translated argument of `h₀` back into `y₀`.
    simpa [p0Block, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum2
  have hfinite_tail :
      ∃ q : (Fin m → ℝ) × (∀ i : Fin m, Fin (ni i) → ℝ), tailBlockProd q < (⊤ : EReal) := by
    let c : Fin m → ℝ := fun i => (data.aStar i ⬝ᵥ x : ℝ) + data.α i
    let v0 : Fin m → ℝ := fun i =>
      (data.h i ((data.A i).mulVec x + data.a i) + ((c i : ℝ) : EReal)).toReal
    let pZero : ∀ i : Fin m, Fin (ni i) → ℝ := fun i => 0
    have hx_feas :
        x ∈ intermediateProgramFeasibleSet data
          ({ v := v0, p0 := (0 : Fin n0 → ℝ), p := pZero } :
            IntermediateProgramParameter m n n0 ni) := by
      intro i
      have hvalue_top :
          data.h i ((data.A i).mulVec x + data.a i) < (⊤ : EReal) := by
        exact helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
          (data := data) (i := i) (y := (data.A i).mulVec x + data.a i) (hdomi := hdom i)
      have hterm_ne_top :
          data.h i ((data.A i).mulVec x + data.a i) + ((c i : ℝ) : EReal) ≠ (⊤ : EReal) :=
        EReal.add_ne_top (ne_of_lt hvalue_top) (EReal.coe_ne_top _)
      have hle :
          data.h i ((data.A i).mulVec x + data.a i) + ((c i : ℝ) : EReal) ≤
            (((v0 i : ℝ) : EReal)) := by
        simpa [v0] using
          EReal.le_coe_toReal
            (x := data.h i ((data.A i).mulVec x + data.a i) + ((c i : ℝ) : EReal))
            hterm_ne_top
      simpa [intermediateProgramFeasibleSet, pZero, c, sub_eq_add_neg] using hle
    refine ⟨(v0, pZero), ?_⟩
    have hvalue :
        tailBlockProd (v0, pZero) = (((v0 ⬝ᵥ wStar.vStar : ℝ) : EReal)) := by
      -- At the witness, the indicator vanishes and every translated-coordinate pairing is zero.
      simp [tailBlockProd, tailBlock, pZero, indicatorFunction, hx_feas]
    rw [hvalue]
    exact (lt_top_iff_ne_top).2 (EReal.coe_ne_top _)
  have hsplit_integrand :
      (⨅ w : IntermediateProgramParameter m n n0 ni,
          intermediateProgramBifunction data w x -
            (((x ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w wStar : ℝ) : EReal))) =
        (⨅ v : Fin m → ℝ,
          ⨅ p0 : Fin n0 → ℝ,
            ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
              p0Block p0 + tailBlock v p +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
    rw [helperForTheorem_6_30_24_iInf_parameter_eq_nestedBlocks
      (H := fun w : IntermediateProgramParameter m n n0 ni =>
        intermediateProgramBifunction data w x -
          (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing w wStar : ℝ) : EReal)))]
    refine iInf_congr ?_
    intro v
    refine iInf_congr ?_
    intro p0
    refine iInf_congr ?_
    intro p
    have hIndicator :
        indicatorFunction (intermediateProgramFeasibleSet data
            ({ v := v, p0 := p0, p := p } : IntermediateProgramParameter m n n0 ni)) x =
          indicatorFunction (intermediateProgramFeasibleSet data
            ({ v := v, p0 := (0 : Fin n0 → ℝ), p := p } :
              IntermediateProgramParameter m n n0 ni)) x := by
      rfl
    -- This is exactly the pointwise decomposition into the head block, the tail block, and
    -- the outer subtraction `-⟪x, x*⟫`.
    rw [intermediateProgramBifunction, intermediateProgramDualPairing, hIndicator, sub_eq_add_neg]
    rw [EReal.coe_add, EReal.coe_add]
    rw [helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe]
    simp [p0Block, tailBlock, add_assoc, add_left_comm, add_comm]
  have hswap_p0 :
      (⨅ v : Fin m → ℝ,
          ⨅ p0 : Fin n0 → ℝ,
            ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
              p0Block p0 + tailBlock v p +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
        (⨅ p0 : Fin n0 → ℝ,
          ⨅ v : Fin m → ℝ,
            ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
              p0Block p0 + tailBlock v p +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
    rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested
      (H := fun v : Fin m → ℝ => fun p0 : Fin n0 → ℝ =>
        ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          p0Block p0 + tailBlock v p +
            (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
    have hCommute :
        (⨅ q : (Fin m → ℝ) × (Fin n0 → ℝ),
            ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
              p0Block q.2 + tailBlock q.1 p +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
          (⨅ q : (Fin n0 → ℝ) × (Fin m → ℝ),
            ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
              p0Block q.1 + tailBlock q.2 p +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
          refine (Equiv.iInf_congr (Equiv.prodComm (Fin m → ℝ) (Fin n0 → ℝ)) ?_)
          intro q
          rfl
    rw [hCommute]
    rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
      (H := fun p0 : Fin n0 → ℝ => fun v : Fin m → ℝ =>
        ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          p0Block p0 + tailBlock v p +
            (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
  -- Split the head `p₀` block from the packaged tail block, then substitute the already-proved
  -- block formulas and collect the remaining linear term.
  calc
    (⨅ w : IntermediateProgramParameter m n n0 ni,
        intermediateProgramBifunction data w x -
          (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing w wStar : ℝ) : EReal))) =
      (⨅ p0 : Fin n0 → ℝ,
        ⨅ v : Fin m → ℝ,
          ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
            p0Block p0 + tailBlock v p +
              (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
            rw [hsplit_integrand, hswap_p0]
    _ =
      ((⨅ p0 : Fin n0 → ℝ, p0Block p0) +
          (⨅ v : Fin m → ℝ, ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ, tailBlock v p)) +
        (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
            calc
              (⨅ p0 : Fin n0 → ℝ,
                  ⨅ v : Fin m → ℝ,
                    ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
                      p0Block p0 + tailBlock v p +
                        (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
                (⨅ p0 : Fin n0 → ℝ,
                  ⨅ q : (Fin m → ℝ) × (∀ i : Fin m, Fin (ni i) → ℝ),
                    p0Block p0 + tailBlockProd q +
                      (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
                        refine iInf_congr ?_
                        intro p0
                        symm
                        exact helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := fun v : Fin m → ℝ =>
                            fun p : ∀ i : Fin m, Fin (ni i) → ℝ =>
                              p0Block p0 + tailBlock v p +
                                (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))
              _ =
                ((⨅ p0 : Fin n0 → ℝ, p0Block p0) +
                    (⨅ q : (Fin m → ℝ) × (∀ i : Fin m, Fin (ni i) → ℝ), tailBlockProd q)) +
                  (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
                        rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := fun p0 : Fin n0 → ℝ =>
                            fun q : (Fin m → ℝ) × (∀ i : Fin m, Fin (ni i) → ℝ) =>
                              p0Block p0 + tailBlockProd q +
                                (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
                        rw [helperForTheorem_6_30_22_twoFactor_iInf_add_realConst
                          (F := p0Block) (G := tailBlockProd) (c := -(x ⬝ᵥ xStar : ℝ))
                          hfinite_p0 hfinite_tail]
              _ =
                ((⨅ p0 : Fin n0 → ℝ, p0Block p0) +
                    (⨅ v : Fin m → ℝ,
                      ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ, tailBlock v p)) +
                  (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
                        rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := tailBlock)]
    _ =
      ((((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
          ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
            fenchelConjugate n0 data.h0 wStar.p0)) +
        (∑ i : Fin m,
          ((((x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                ℝ) : EReal)) +
            ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                  ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
              fenchelConjugate (ni i)
                (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                (wStar.p i)))) +
        (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
            rw [helperForTheorem_6_30_24_headBlock_iInf_eq_linear_minus_fenchel
              (data := data) (x := x) (wStar := wStar)]
            rw [helperForTheorem_6_30_24_tailBlock_iInf_eq_sum_constraintBlocks
              (data := data) (hh := hh) (hdom := hdom) (x := x) (wStar := wStar)
              (hnonneg := hnonneg)]
    _ =
      ((((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
          ∑ i : Fin m,
            (((x ⬝ᵥ
                ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                  ℝ) : EReal)) +
          (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) +
        (((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
            fenchelConjugate n0 data.h0 wStar.p0) +
        ∑ i : Fin m,
            ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                  ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
              fenchelConjugate (ni i)
                (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                (wStar.p i))) := by
            let A : EReal :=
              (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal))
            let B : EReal :=
              ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
                fenchelConjugate n0 data.h0 wStar.p0)
            let C : EReal :=
              ∑ i : Fin m,
                (((x ⬝ᵥ
                    ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                      ℝ) : EReal))
            let D : EReal :=
              ∑ i : Fin m,
                ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                      ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
                  fenchelConjugate (ni i)
                    (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                    (wStar.p i))
            let E : EReal := (((-(x ⬝ᵥ xStar) : ℝ) : EReal))
            simp_rw [sub_eq_add_neg]
            rw [Finset.sum_add_distrib]
            change ((A + B) + (C + D)) + E = (((A + C) + E) + (B + D))
            calc
              ((A + B) + (C + D)) + E = A + (B + (C + (D + E))) := by
                simp [add_assoc]
              _ = A + (C + (E + (B + D))) := by
                congr 1
                calc
                  B + (C + (D + E)) = B + C + (E + D) := by
                    rw [add_comm D E]
                    simp [add_assoc]
                  _ = B + (C + E) + D := by
                    have htmp : B + C + (E + D) = B + (C + E) + D := by
                      simp [add_assoc]
                    exact htmp
                  _ = (C + E + B) + D := by
                    rw [add_comm B (C + E)]
                  _ = C + (E + B) + D := by
                    have htmp : (C + E + B) + D = C + (E + B) + D := by
                      simp [add_assoc]
                    exact htmp
                  _ = C + (E + (B + D)) := by
                    simp [add_assoc]
              _ = (((A + C) + E) + (B + D)) := by
                simp [add_assoc]
    _ =
      (((x ⬝ᵥ
          (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) :
          EReal)) +
        (((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
            fenchelConjugate n0 data.h0 wStar.p0) +
          ∑ i : Fin m,
            ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                  ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
              fenchelConjugate (ni i)
                (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                (wStar.p i))) := by
            let K : EReal :=
              (((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
                    fenchelConjugate n0 data.h0 wStar.p0) +
                  ∑ i : Fin m,
                    ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                          ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
                      fenchelConjugate (ni i)
                        (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                        (wStar.p i)))
            let L : EReal :=
              (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
                ∑ i : Fin m,
                  (((x ⬝ᵥ
                      ((wStar.vStar i) • data.aStar i +
                          (data.A i).transpose.mulVec (wStar.p i)) : ℝ) : EReal)) +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))
            have hL :
                L =
                  (((x ⬝ᵥ
                      (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) :
                      EReal)) := by
              simpa [L] using
                (helperForTheorem_6_30_24_translationLinearTerms_collect
                  (data := data) (x := x) (xStar := xStar) (wStar := wStar))
            simpa [L, K] using congrArg (fun t : EReal => t + K) hL
    _ =
      (((x ⬝ᵥ
          (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) :
          EReal)) +
        intermediateProgramDualObjective data wStar := by
            rw [intermediateProgramDualObjective]

/-- Helper for Theorem 6.30.24: on the branch `v* ≥ 0`, the adjoint rewrites as the infimum of a
free linear term in `x` plus the explicit dual objective. -/
lemma helperForTheorem_6_30_24_adjoint_rewrite_of_nonnegativeMultipliers
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ)
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.vStar i) :
    adjointOfIntermediateProgram data xStar wStar =
      sInf (Set.range fun x : Fin n → ℝ =>
        (((x ⬝ᵥ
            (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) : EReal)) +
          intermediateProgramDualObjective data wStar) := by
  -- Rewrite the adjoint as an outer infimum over `x`, then collapse the inner parameter infimum
  -- pointwise by the fixed-`x` helper.
  rw [adjointOfIntermediateProgram, sInf_range]
  have hCommute :
      (⨅ p : IntermediateProgramParameter m n n0 ni × (Fin n → ℝ),
          intermediateProgramBifunction data p.1 p.2 -
            (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing p.1 wStar : ℝ) : EReal))) =
        (⨅ p : (Fin n → ℝ) × IntermediateProgramParameter m n n0 ni,
          intermediateProgramBifunction data p.2 p.1 -
            (((p.1 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing p.2 wStar : ℝ) : EReal))) := by
    refine (Equiv.iInf_congr
      (Equiv.prodComm (IntermediateProgramParameter m n n0 ni) (Fin n → ℝ)) ?_)
    intro p
    rfl
  calc
    (⨅ p : IntermediateProgramParameter m n n0 ni × (Fin n → ℝ),
        intermediateProgramBifunction data p.1 p.2 -
          (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing p.1 wStar : ℝ) : EReal))) =
      (⨅ p : (Fin n → ℝ) × IntermediateProgramParameter m n n0 ni,
        intermediateProgramBifunction data p.2 p.1 -
          (((p.1 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing p.2 wStar : ℝ) : EReal))) := hCommute
    _ =
      (⨅ x : Fin n → ℝ,
        ⨅ w : IntermediateProgramParameter m n n0 ni,
          intermediateProgramBifunction data w x -
            (((x ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w wStar : ℝ) : EReal))) := by
              rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
                (H := fun x : Fin n → ℝ =>
                  fun w : IntermediateProgramParameter m n n0 ni =>
                    intermediateProgramBifunction data w x -
                      (((x ⬝ᵥ xStar : ℝ) : EReal)) +
                      (((intermediateProgramDualPairing w wStar : ℝ) : EReal)))]
    _ =
      (⨅ x : Fin n → ℝ,
        (((x ⬝ᵥ
            (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) : EReal)) +
          intermediateProgramDualObjective data wStar) := by
              refine iInf_congr ?_
              intro x
              exact helperForTheorem_6_30_24_fixedX_parameterInf_eq_linearPlusDualObjective
                (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)
                (x := x) (xStar := xStar) (wStar := wStar) hnonneg
    _ =
      sInf (Set.range fun x : Fin n → ℝ =>
        (((x ⬝ᵥ
            (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) : EReal)) +
          intermediateProgramDualObjective data wStar) := by
              rw [sInf_range]

/-- Helper for Theorem 6.30.24: on the dual-feasible branch, the nonnegative adjoint rewrite
collapses to the explicit dual objective because the balance vector equals `x*`. -/
lemma helperForTheorem_6_30_24_adjoint_eq_dualObjective_of_dualFeasible
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ)
    {xStar : Fin n → ℝ} {wStar : IntermediateProgramDualParameter m n n0 ni}
    (hfeas : intermediateProgramDualFeasible data xStar wStar) :
    adjointOfIntermediateProgram data xStar wStar =
      intermediateProgramDualObjective data wStar := by
  -- First rewrite the adjoint into the free linear term plus the explicit dual objective.
  rw [helperForTheorem_6_30_24_adjoint_rewrite_of_nonnegativeMultipliers
    (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)
    (xStar := xStar) (wStar := wStar) (hnonneg := hfeas.1)]
  -- On the feasible branch the linear coefficient vanishes, so the ranged family is constant.
  simp [helperForTheorem_6_30_24_dualBalanceVector, hfeas.2]

/-- Helper for Theorem 6.30.24: on the nonnegative branch, if the balance vector does not equal
`x*`, then the free linear term has nonzero coefficient and the adjoint value is `-∞`. -/
lemma helperForTheorem_6_30_24_adjoint_eq_bot_of_nonnegative_and_balanceMismatch
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ)
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.vStar i)
    (hbalance_ne : helperForTheorem_6_30_24_dualBalanceVector data wStar ≠ xStar) :
    adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal) := by
  have hMismatch :
      helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar ≠ 0 := by
    -- A zero difference would force the missing balance equality.
    intro hzero
    apply hbalance_ne
    exact sub_eq_zero.mp hzero
  -- Rewrite the adjoint by the nonnegative-branch formula and use the nonzero linear term to
  -- drive the infimum to `⊥`.
  rw [helperForTheorem_6_30_24_adjoint_rewrite_of_nonnegativeMultipliers
    (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)
    (xStar := xStar) (wStar := wStar) (hnonneg := hnonneg)]
  exact helperForTheorem_6_30_22_sInf_linear_plus_nonTopConst_eq_bot_of_ne_zero
    (b := helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar)
    (c := intermediateProgramDualObjective data wStar)
    hMismatch
    (helperForTheorem_6_30_24_dualObjective_ne_top_of_nonnegative
      (data := data) (hh0 := hh0) (hh := hh) (wStar := wStar) (hnonneg := hnonneg))

/-- Helper for Theorem 6.30.24: the remaining core task is the branchwise adjoint formula under
the additional full-domain hypothesis. This isolates the exact first conjunct of the theorem so
the second conjunct stays the already definitional `sSup` identity. -/
lemma helperForTheorem_6_30_24_branchFormulas_of_fullDomain
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ) :
    ∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
      (intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar =
          intermediateProgramDualObjective data wStar) ∧
      (¬ intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal)) := by
  intro xStar wStar
  constructor
  · -- The feasible branch is exactly the explicit adjoint formula on the nonnegative rewrite.
    intro hfeas
    exact helperForTheorem_6_30_24_adjoint_eq_dualObjective_of_dualFeasible
      (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom) hfeas
  · -- Split infeasibility into the finished negative-multiplier case and the remaining
    -- nonnegative balance-mismatch branch.
    intro hnotfeas
    rcases
        (helperForTheorem_6_30_24_not_dualFeasible_iff_exists_negativeMultiplier_or_balanceMismatch
          (data := data) (xStar := xStar) (wStar := wStar)).1 hnotfeas with
      hneg | ⟨hnonneg, hbalance_ne⟩
    · exact helperForTheorem_6_30_24_adjoint_eq_bot_of_exists_negativeMultiplier
        (data := data) (hh0 := hh0) (hh := hh) (xStar := xStar) (wStar := wStar) hneg
    · exact helperForTheorem_6_30_24_adjoint_eq_bot_of_nonnegative_and_balanceMismatch
        (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)
        (xStar := xStar) (wStar := wStar) hnonneg hbalance_ne

/-- Helper for Theorem 6.30.24: the full-domain branch formulas together with the definitional
dual-value identity already package the exact theorem conclusion. -/
lemma helperForTheorem_6_30_24_fullDomainConclusion
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ) :
    (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
      (intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar =
          intermediateProgramDualObjective data wStar) ∧
      (¬ intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
    dualProgramValueOfIntermediateProgram data =
      sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
        intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
          v = intermediateProgramDualObjective data wStar} := by
  refine ⟨?_, ?_⟩
  · -- The first conjunct is the already isolated full-domain branch formula.
    exact helperForTheorem_6_30_24_branchFormulas_of_fullDomain
      (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)
  · -- The second conjunct is the definitional `sSup` expression for the dual program value.
    exact helperForTheorem_6_30_24_dualProgramValue_eq_explicitSup data

-- Proof sketch: view the intermediate program as the enlarged-perturbation program attached to
-- the affine constraint representation `fᵢ(x) = hᵢ(Aᵢ x + aᵢ) + ⟪aᵢ*, x⟫ + αᵢ`, then specialize the
-- general adjoint formula of Theorem 6.30.22. The affine shifts contribute the linear terms
-- `⟪aᵢ, pᵢ*⟫` and the balance equation involving `aᵢ*` and `Aᵢ* pᵢ*`, while the conjugate terms
-- become the Fenchel conjugates of the scaled functions `vᵢ* hᵢ`. Evaluating at `x* = 0` yields
-- the stated dual maximization problem.
/-- Theorem 6.30.24: for affine-represented constraint functions
`fᵢ(x) = hᵢ(Aᵢ x + aᵢ) + ⟪aᵢ*, x⟫ + αᵢ`, with each `hᵢ` closed proper convex and everywhere finite,
the adjoint of the intermediate-program bifunction agrees with
`intermediateProgramDualObjective` on the feasible set `intermediateProgramDualFeasible` and is
`-∞` otherwise. Consequently, the dual program `(R*)` maximizes
`intermediateProgramDualObjective` subject to those feasibility constraints. -/
theorem adjointFormula_and_dualProgram_for_intermediateProgram {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (hdom : ∀ i : Fin m,
      effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ) :
    (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
      (intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar =
          intermediateProgramDualObjective data wStar) ∧
      (¬ intermediateProgramDualFeasible data xStar wStar →
        adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
    dualProgramValueOfIntermediateProgram data =
      sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
        intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
          v = intermediateProgramDualObjective data wStar} := by
  -- Reuse the packaged full-domain conclusion so the theorem body stays aligned with the
  -- preceding helper chain.
  exact helperForTheorem_6_30_24_fullDomainConclusion
    (data := data) (hh0 := hh0) (hh := hh) (hdom := hdom)


end Section30
end Chap06
