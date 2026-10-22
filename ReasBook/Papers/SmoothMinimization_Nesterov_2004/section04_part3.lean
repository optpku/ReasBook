/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section04_part2

open scoped NNReal

set_option maxHeartbeats 350000 in
/-- Theorem 1.4.1.
Assume the structural model (2.2) and that `fhat` is differentiable with M-Lipschitz gradient on
`Q1`. Let `d1` be a prox-function of `Q1` with parameter `σ1 > 0` and prox-diameter `D1` as in
(4.3_D1). Let `d2` be a prox-function of `Q2` with strong convexity parameter `σ2 > 0` and define
`D2 := max_{u ∈ Q2} d2 u` as in Proposition 2.7. Apply Algorithm 3.11 to the smoothed problem
(4.1) with `μ = μ(N) = (2‖A‖_{1,2}/(N+1)) * sqrt(D1/(σ1 σ2 D2))` (equation (thm3_muN)). After `N`
iterations define `\hat x := y_N` and
`\hat u := ∑_{i=0}^N 2(i+1)/((N+1)(N+2)) u_μ(x_i)` (4.2). Then `0 ≤ f(\hat x) - φ(\hat u)` and the
duality-gap bound (4.3) holds, and consequently the ε-solution bound (4.4) holds. -/
theorem algorithm311_duality_gap_bound {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (fhat : E1 → ℝ) (phihat : E2 → ℝ)
    (d1 : E1 → ℝ) (d2 : E2 → ℝ) (σ1 σ2 M D1 : ℝ) (xSeq ySeq : ℕ → Q1) (uμ : E1 → E2)
    (N : ℕ) (hatu : Q2) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    let D2 : ℝ := sSup (d2 '' Q2)
    let μ : ℝ :=
      (2 * OperatorNormDef A' / ((N : ℝ) + 1)) *
        Real.sqrt (D1 / (σ1 * σ2 * D2))
    let fbar : E1 → ℝ := SmoothedObjective Q2 A phihat d2 μ fhat
    let f : E1 → ℝ := fun x => fhat x + sSup ((fun u => A x u - phihat u) '' Q2)
    let φ : Q2 → ℝ := AdjointFormPotential Q1 Q2 A fhat phihat
    LipschitzOnWith (Real.toNNReal M) (fun x => fderiv ℝ fhat x) Q1 →
    0 < σ1 →
    0 < σ2 →
    StrongConvexOn Q1 σ1 d1 →
    StrongConvexOn Q2 σ2 d2 →
    IsProxDiameterBound Q1 d1 D1 →
    OptimalSchemeAlgorithm Q1 fbar d1
      (M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2) σ1 xSeq ySeq →
    (∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) →
    (hatu : E2) =
      Finset.sum (Finset.range (N + 1)) (fun i =>
        (2 * ((i : ℝ) + 1) / (((N : ℝ) + 1) * ((N : ℝ) + 2))) •
          uμ (xSeq i : E1)) →
    ConvexOn ℝ Q1 fhat →
    DifferentiableOn ℝ fhat Q1 →
    ConvexOn ℝ Q2 phihat →
    (∀ x,
      fderiv ℝ (SmoothedMaxFunction Q2 A phihat d2 μ) x =
        (AdjointOperator A' (uμ x)).toContinuousLinearMap) →
    0 ≤ M →
    0 ≤ D1 →
    0 < M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2 →
    IsClosed Q1 →
    IsOpen Q1 →
    ConvexOn ℝ Q1 fbar →
    DifferentiableOn ℝ fbar Q1 →
    0 ≤ μ →
    (∀ u ∈ Q2, 0 ≤ d2 u) →
    (∀ x, BddAbove ((fun u => A x u - phihat u) '' Q2)) →
    BddAbove (d2 '' Q2) →
    Q2.Nonempty →
    (∀ u, BddBelow ((fun x => A x u + fhat x) '' Q1)) →
    0 ≤ f (ySeq N : E1) - φ hatu ∧
      f (ySeq N : E1) - φ hatu ≤
        (4 * OperatorNormDef A' / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) +
          (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) ∧
      ∀ ε > 0,
        (N : ℝ) ≥
          (4 * OperatorNormDef A' / ε) * Real.sqrt (D1 * D2 / (σ1 * σ2)) +
            2 * Real.sqrt (M * D1 / (σ1 * ε)) →
          f (ySeq N : E1) - φ hatu ≤ ε := by
  classical
  dsimp
  intro hLipschitz hσ1 hσ2 hconv1 hconv2 hD1 hAlg hmax hhatudef
    hfhat_convex hfhat_diff hphihat_convex hderivμ hM_nonneg hD1_nonneg hL_pos
    hQ1_closed hQ1_open hfbar_convex hfbar_diff hμ_nonneg hd2_nonneg hbd0 hbd_d2 hQ2_nonempty
    hbdBelow
  set A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro c x
        ext u
        simp } with hA'
  set μ : ℝ :=
    (2 * OperatorNormDef A' / ((N : ℝ) + 1)) *
      Real.sqrt (D1 / (σ1 * σ2 * sSup (d2 '' Q2))) with hμ_def
  set f : E1 → ℝ := fun x => fhat x + sSup ((fun u => A x u - phihat u) '' Q2) with hf
  set φ : Q2 → ℝ := AdjointFormPotential Q1 Q2 A fhat phihat with hφ
  have hμ_nonneg' : 0 ≤ μ := by
    simpa [hA', hμ_def] using hμ_nonneg
  have hD2_nonneg : 0 ≤ sSup (d2 '' Q2) := by
    refine sSup_image_nonneg (s := Q2) (f := d2) (hbd := hbd_d2) (hne := hQ2_nonempty)
      ?_
    intro u hu
    exact hd2_nonneg u hu
  have hgap_nonneg :
      0 ≤
        (fhat (ySeq N : E1) + sSup ((fun u => A (ySeq N : E1) u - phihat u) '' Q2)) -
          AdjointFormPotential Q1 Q2 A fhat phihat hatu := by
    have hdual :=
      adjointForm_duality_gap_nonneg (Q1 := Q1) (Q2 := Q2) (A := A) (fhat := fhat)
        (phihat := phihat) (hbd0 := hbd0) (hbdBelow := hbdBelow)
    have hy : (ySeq N : E1) ∈ Q1 := (ySeq N).property
    exact hdual (x := (ySeq N : E1)) hy (u := hatu)
  have hsmoothed :
      fhat (ySeq N : E1) + sSup ((fun u => A (ySeq N : E1) u - phihat u) '' Q2) ≤
        SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + μ * sSup (d2 '' Q2) := by
    have hbound :=
      smoothedObjective_bound (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2) (μ := μ)
        (fhat := fhat)
    simpa using (hbound (x := (ySeq N : E1)) hμ_nonneg' hd2_nonneg hbd0 hbd_d2)
  have hgap_smoothed :
      (fhat (ySeq N : E1) + sSup ((fun u => A (ySeq N : E1) u - phihat u) '' Q2)) -
          AdjointFormPotential Q1 Q2 A fhat phihat hatu ≤
        μ * sSup (d2 '' Q2) +
          (SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
            AdjointFormPotential Q1 Q2 A fhat phihat hatu) := by
    have h' :=
      sub_le_sub_right hsmoothed (AdjointFormPotential Q1 Q2 A fhat phihat hatu)
    -- regroup the right-hand side as `μ * D2 + (fbar - φ)`
    have h'' :
        (SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + μ * sSup (d2 '' Q2)) -
            AdjointFormPotential Q1 Q2 A fhat phihat hatu =
          μ * sSup (d2 '' Q2) +
            (SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
              AdjointFormPotential Q1 Q2 A fhat phihat hatu) := by
      ring
    exact le_trans h' (le_of_eq h'')
  refine And.intro hgap_nonneg ?_
  have hgap_fbar :
      SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
          AdjointFormPotential Q1 Q2 A fhat phihat hatu ≤
        (4 * (M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2) * D1) /
          (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    have hQ1_convex : Convex ℝ Q1 := convex_of_strongConvexOn hconv1
    set L : ℝ := M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2
    set denom : ℝ := ((N : ℝ) + 1) * ((N : ℝ) + 2)
    have hdenom_expr : ((N : ℝ) + 1) * ((N : ℝ) + 2) = denom := by
      simp [denom]
    have hdenom_div2 : ((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 = denom / 2 := by
      simpa using congrArg (fun z : ℝ => z / 2) hdenom_expr
    have hL_pos' : 0 < L := by
      simpa [L] using hL_pos
    have hdenom_pos : 0 < denom := by
      have h1 : 0 < (N : ℝ) + 1 := by
        exact_mod_cast (Nat.succ_pos N)
      have h2 : 0 < (N : ℝ) + 2 := by
        exact_mod_cast (Nat.succ_pos (N + 1))
      simpa [denom] using mul_pos h1 h2
    have hcoef : (2 / denom) * (denom / 2) = (1 : ℝ) := by
      field_simp [denom, hdenom_pos.ne']
    have hpair : ∀ x u, DualPairing (AdjointOperator A' u) x = A x u := by
      intro x u
      simp [AdjointOperator, DualPairing, hA']
    have hbound_all :
        ∀ x ∈ Q1,
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu -
              (4 * L * D1) / (σ1 * denom) ≤ A x hatu + fhat x := by
      intro x hx
      have hrate :=
        fbar_rate_bound (xSeq := xSeq) (ySeq := ySeq) (N := N) (Q := Q1)
          (f := SmoothedObjective Q2 A phihat d2 μ fhat) (d := d1) (L := L) (σ := σ1) (D := D1)
          (hL := hL_pos') (hσ := hσ1) (hAlg := hAlg) (hD := hD1) hx
      have hsum_bound :=
        weighted_sum_bound_hatu (Q1 := Q1) (Q2 := Q2) (A := A) (fhat := fhat)
          (phihat := phihat) (d2 := d2) (μ := μ) (uμ := uμ) (A' := A') (xSeq := xSeq) (N := N)
          (hatu := hatu) hhatudef (hQ1_open := hQ1_open) (hQ1_convex := hQ1_convex)
          (hfhat_convex := hfhat_convex) (hfhat_diff := hfhat_diff) (hfbar_diff := hfbar_diff)
          (hphihat_convex := hphihat_convex) (hμ_nonneg := hμ_nonneg) (hd2_nonneg := hd2_nonneg)
          (hmax := hmax) (hderivμ := hderivμ) (hpair := hpair) x hx
      have hcoef_nonneg : 0 ≤ 2 / denom := by
        exact div_nonneg (by norm_num) (le_of_lt hdenom_pos)
      have hsum_mul :=
        mul_le_mul_of_nonneg_left hsum_bound hcoef_nonneg
      have hrate_comm :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) ≤
            (4 * L * D1) / (σ1 * denom) +
              (2 / denom) *
                ∑ i ∈ Finset.range (N + 1),
                  (↑i + 1) *
                    (SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
                      DualPairing
                        ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
                        (x - xSeq i)) := by
        simpa [hdenom_expr] using hrate
      have hrate_sum :
          (4 * L * D1) / (σ1 * denom) +
                (2 / denom) *
                  ∑ i ∈ Finset.range (N + 1),
                    (↑i + 1) *
                      (SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
                        DualPairing
                          ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
                          (x - xSeq i)) ≤
              (4 * L * D1) / (σ1 * denom) +
                (2 / denom) *
                  (((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 * (fhat x + A x hatu - phihat hatu)) := by
        exact add_le_add_right hsum_mul ((4 * L * D1) / (σ1 * denom))
      have hrate_tmp := le_trans hrate_comm hrate_sum
      have hrate' :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) ≤
            (4 * L * D1) / (σ1 * denom) +
              (2 / denom) * ((denom / 2) * (fhat x + A x hatu - phihat hatu)) := by
        have hrhs :
            (4 * L * D1) / (σ1 * denom) +
                  (2 / denom) *
                    (((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 * (fhat x + A x hatu - phihat hatu)) =
                (4 * L * D1) / (σ1 * denom) +
                  (2 / denom) * ((denom / 2) * (fhat x + A x hatu - phihat hatu)) := by
          rw [hdenom_div2]
        exact le_trans hrate_tmp (le_of_eq hrhs)
      have hrate'' :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) ≤
            (4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu - phihat hatu) := by
        have hrhs :
            (4 * L * D1) / (σ1 * denom) +
                (2 / denom) * ((denom / 2) * (fhat x + A x hatu - phihat hatu)) =
              (4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu - phihat hatu) := by
          -- reassociate then cancel the coefficient using `hcoef`
          have hcancel :
              (2 / denom) * ((denom / 2) * (fhat x + A x hatu - phihat hatu)) =
                (fhat x + A x hatu - phihat hatu) := by
            calc
              (2 / denom) * ((denom / 2) * (fhat x + A x hatu - phihat hatu)) =
                  ((2 / denom) * (denom / 2)) * (fhat x + A x hatu - phihat hatu) := by
                simpa [mul_assoc] using
                  (mul_assoc (2 / denom) (denom / 2) (fhat x + A x hatu - phihat hatu)).symm
              _ = (1 : ℝ) * (fhat x + A x hatu - phihat hatu) := by
                rw [hcoef]
              _ = fhat x + A x hatu - phihat hatu := by
                simp
          simp [hcancel]
        exact le_trans hrate' (le_of_eq hrhs)
      refine (sub_le_iff_le_add).2 ?_
      have hrate_add := add_le_add hrate'' (le_rfl : phihat hatu ≤ phihat hatu)
      -- `(+ phihat hatu)` cancels the `(- phihat hatu)` on the right.
      have hrate_add' :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu ≤
            (4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu) := by
        have hrhs :
            ((4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu - phihat hatu)) + phihat hatu =
              (4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu) := by
          ring
        exact le_trans hrate_add (le_of_eq hrhs)
      have hrhs :
          (4 * L * D1) / (σ1 * denom) + (fhat x + A x hatu) =
            A x hatu + fhat x + (4 * L * D1) / (σ1 * denom) := by
        ring
      exact le_trans hrate_add' (le_of_eq hrhs)
    have hbound_inf :
        SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu -
            (4 * L * D1) / (σ1 * denom) ≤
          sInf ((fun x => A x hatu + fhat x) '' Q1) := by
      have hnonempty : ((fun x => A x hatu + fhat x) '' Q1).Nonempty := by
        refine ⟨A (xSeq 0 : E1) hatu + fhat (xSeq 0 : E1), ?_⟩
        exact ⟨xSeq 0, (xSeq 0).property, rfl⟩
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hbound_all x hx
    have hgap :
        SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
            AdjointFormPotential Q1 Q2 A fhat phihat hatu ≤
          (4 * L * D1) / (σ1 * denom) := by
      have hφ :
          AdjointFormPotential Q1 Q2 A fhat phihat hatu =
            -phihat hatu + sInf ((fun x => A x hatu + fhat x) '' Q1) := by
        rfl
      have hle :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu ≤
            sInf ((fun x => A x hatu + fhat x) '' Q1) + (4 * L * D1) / (σ1 * denom) := by
        exact (sub_le_iff_le_add).1 hbound_inf
      have hsub :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu -
              sInf ((fun x => A x hatu + fhat x) '' Q1) ≤
            (4 * L * D1) / (σ1 * denom) := by
        have := sub_le_sub_right hle (sInf ((fun x => A x hatu + fhat x) '' Q1))
        -- simplify the right-hand side `(sInf + C) - sInf`
        have hrhs :
            (sInf ((fun x => A x hatu + fhat x) '' Q1) + (4 * L * D1) / (σ1 * denom)) -
                sInf ((fun x => A x hatu + fhat x) '' Q1) =
              (4 * L * D1) / (σ1 * denom) := by
          ring
        simpa [hrhs] using this
      -- rewrite `fbar - φ` as `fbar + phihat - sInf`
      have hrewrite :
          SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
              AdjointFormPotential Q1 Q2 A fhat phihat hatu =
            SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) + phihat hatu -
              sInf ((fun x => A x hatu + fhat x) '' Q1) := by
        rw [hφ]
        ring
      simpa [hrewrite] using hsub
    simpa [L, denom, mul_assoc] using hgap
  have hgap_bound :
      f (ySeq N : E1) - φ hatu ≤
        μ * sSup (d2 '' Q2) +
          (4 * (M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2) * D1) /
            (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    have h2' :
        μ * sSup (d2 '' Q2) +
            (SmoothedObjective Q2 A phihat d2 μ fhat (ySeq N : E1) -
              AdjointFormPotential Q1 Q2 A fhat phihat hatu) ≤
          μ * sSup (d2 '' Q2) +
            (4 * (M + (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2) * D1) /
              (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
      exact
        add_le_add (le_rfl : μ * sSup (d2 '' Q2) ≤ μ * sSup (d2 '' Q2)) hgap_fbar
    have h' := le_trans hgap_smoothed h2'
    simpa [hf, hφ] using h'
  have hgap_bound' :
      f (ySeq N : E1) - φ hatu ≤
        (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
            Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) +
          (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) := by
    set D2 : ℝ := sSup (d2 '' Q2)
    set denom : ℝ := ((N : ℝ) + 1) * ((N : ℝ) + 2)
    set K : ℝ := (1 / (μ * σ2)) * (OperatorNormDef A') ^ 2
    have hdenom_pos : 0 < denom := by
      have h1 : 0 < (N : ℝ) + 1 := by
        exact_mod_cast (Nat.succ_pos N)
      have h2 : 0 < (N : ℝ) + 2 := by
        exact_mod_cast (Nat.succ_pos (N + 1))
      simpa [denom] using mul_pos h1 h2
    have hμterm :
        μ * D2 +
            (4 * K * D1) / (σ1 * denom) ≤
          (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
            Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
      have hAop_nonneg : 0 ≤ OperatorNormDef A' := operatorNormDef_nonneg (A := A')
      have hμ_def' :
          μ = (2 * OperatorNormDef A' / ((N : ℝ) + 1)) *
              Real.sqrt (D1 / (σ1 * σ2 * D2)) := by
        simpa [D2] using hμ_def
      have hμterm' :=
        mu_simplify_bound (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ) (N := N)
          (Aop := OperatorNormDef A') hμ_def' hD1_nonneg hD2_nonneg hσ1 hσ2 hAop_nonneg
      simpa [K, denom, mul_assoc] using hμterm'
    have hgap_bound'' :
        f (ySeq N : E1) - φ hatu ≤
          μ * D2 +
            (4 * M * D1) / (σ1 * denom) +
              (4 * K * D1) / (σ1 * denom) := by
      have hgap := hgap_bound
      have hgap' :
          f (ySeq N : E1) - φ hatu ≤
            μ * D2 +
              (4 * (M + K) * D1) /
                (σ1 * denom) := by
        simpa [D2, denom, K, mul_assoc] using hgap
      have hsplit :
          μ * D2 +
              (4 * (M + K) * D1) /
                (σ1 * denom) =
            μ * D2 +
              (4 * M * D1) / (σ1 * denom) +
                (4 * K * D1) / (σ1 * denom) := by
        ring_nf
      have hgap'' :
          f (ySeq N : E1) - φ hatu ≤
            μ * D2 +
              (4 * M * D1) / (σ1 * denom) +
                (4 * K * D1) / (σ1 * denom) := by
        simpa [hsplit] using hgap'
      exact hgap''
    have hMterm :
        (4 * M * D1) / (σ1 * denom) ≤
          (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) := by
      have hnum_nonneg : 0 ≤ 4 * M * D1 := by nlinarith [hM_nonneg, hD1_nonneg]
      have hdenom_le :
          σ1 * ((N : ℝ) + 1) ^ (2 : ℕ) ≤ σ1 * denom := by
        have h' : ((N : ℝ) + 1) ^ (2 : ℕ) ≤ denom := by
          have hpos : 0 ≤ (N : ℝ) + 1 := by
            exact_mod_cast (Nat.zero_le (N + 1))
          have hle : (N : ℝ) + 1 ≤ (N : ℝ) + 2 := by
            exact_mod_cast (Nat.le_succ (N + 1))
          have hmul :
              ((N : ℝ) + 1) * ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
            exact mul_le_mul_of_nonneg_left hle hpos
          simpa [pow_two, denom] using hmul
        have hσ1_nonneg : 0 ≤ σ1 := le_of_lt hσ1
        exact mul_le_mul_of_nonneg_left h' hσ1_nonneg
      have hdenom_pos : 0 < σ1 * ((N : ℝ) + 1) ^ (2 : ℕ) := by
        have hNpos : 0 < (N : ℝ) + 1 := by
          exact_mod_cast (Nat.succ_pos N)
        have hpow_pos : 0 < ((N : ℝ) + 1) ^ (2 : ℕ) := by
          exact pow_pos hNpos 2
        exact mul_pos hσ1 hpow_pos
      exact (div_le_div_of_nonneg_left hnum_nonneg hdenom_pos hdenom_le)
    have hgap_bound''' :
        f (ySeq N : E1) - φ hatu ≤
          (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
              Real.sqrt (D1 * D2 / (σ1 * σ2)) +
            (4 * M * D1) / (σ1 * denom) := by
      set A : ℝ := (4 * M * D1) / (σ1 * denom)
      set B : ℝ := (4 * K * D1) / (σ1 * denom)
      have hgap_bound''_ab :
          f (ySeq N : E1) - φ hatu ≤ μ * D2 + B + A := by
        have hgap' : f (ySeq N : E1) - φ hatu ≤ μ * D2 + A + B := by
          dsimp [A, B]
          exact hgap_bound''
        have hrhs : μ * D2 + A + B = μ * D2 + B + A := by
          abel
        exact le_trans hgap' (le_of_eq hrhs)
      have hμterm' : μ * D2 + B + A ≤
          (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
              Real.sqrt (D1 * D2 / (σ1 * σ2)) + A := by
        have hμtermB :
            μ * D2 + B ≤
              (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
                  Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
          dsimp [B]
          exact hμterm
        exact add_le_add_left hμtermB A
      exact le_trans hgap_bound''_ab hμterm'
    have hgap_bound'''' :
        f (ySeq N : E1) - φ hatu ≤
          (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
              Real.sqrt (D1 * D2 / (σ1 * σ2)) +
            (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) := by
      set T : ℝ :=
        (4 * OperatorNormDef A' / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2))
      have hadd : T + (4 * M * D1) / (σ1 * denom) ≤ T + (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) := by
        exact add_le_add (le_rfl : T ≤ T) hMterm
      have hgap' :
          f (ySeq N : E1) - φ hatu ≤ T + (4 * M * D1) / (σ1 * denom) := by
        dsimp [T]
        exact hgap_bound'''
      exact le_trans hgap' hadd
    dsimp [D2] at hgap_bound''''
    exact hgap_bound''''
  refine And.intro hgap_bound' ?_
  intro ε hε hN
  set a : ℝ :=
    4 * OperatorNormDef A' * Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2))
  set b : ℝ := 4 * M * D1 / σ1
  have ha : 0 ≤ a := by
    have hAop : 0 ≤ OperatorNormDef A' := operatorNormDef_nonneg (A := A')
    have hsqrt : 0 ≤ Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) := by
      exact Real.sqrt_nonneg _
    nlinarith [hAop, hsqrt]
  have hb : 0 ≤ b := by
    have hσ1_nonneg : 0 ≤ σ1 := le_of_lt hσ1
    have hnum_nonneg : 0 ≤ 4 * M * D1 := by
      have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
      have h4M_nonneg : 0 ≤ 4 * M := mul_nonneg h4_nonneg hM_nonneg
      exact mul_nonneg h4M_nonneg hD1_nonneg
    dsimp [b]
    exact div_nonneg hnum_nonneg hσ1_nonneg
  have hN' :
      (N : ℝ) + 1 ≥ a / ε + Real.sqrt (b / ε) := by
    have hAop :
        (4 * OperatorNormDef A' / ε) *
            Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) =
          a / ε := by
      dsimp [a]
      simpa using
        (div_mul_eq_mul_div (4 * OperatorNormDef A') ε
          (Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2))))
    have hB : 2 * Real.sqrt (M * D1 / (σ1 * ε)) = Real.sqrt (b / ε) := by
      have hbε : b / ε = 4 * (M * D1 / (σ1 * ε)) := by
        dsimp [b]
        calc
          (4 * M * D1 / σ1) / ε = (4 * M * D1) / (σ1 * ε) := by
            simp [div_div, mul_assoc]
          _ = (4 * (M * D1)) / (σ1 * ε) := by simp [mul_assoc]
          _ = 4 * (M * D1 / (σ1 * ε)) := by
            simpa [mul_assoc] using (mul_div_assoc (4 : ℝ) (M * D1) (σ1 * ε))
      -- rewrite the right-hand side using `hbε`
      rw [hbε]
      have hs :
          Real.sqrt (4 * (M * D1 / (σ1 * ε))) =
            (2 : ℝ) * Real.sqrt (M * D1 / (σ1 * ε)) := by
        have h :=
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (M * D1 / (σ1 * ε))
        have hsqrt4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
          have h :=
            Real.sqrt_mul_self (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
          simpa [show (2 : ℝ) * 2 = 4 by norm_num] using h
        calc
          Real.sqrt (4 * (M * D1 / (σ1 * ε))) =
              Real.sqrt 4 * Real.sqrt (M * D1 / (σ1 * ε)) := h
          _ = (2 : ℝ) * Real.sqrt (M * D1 / (σ1 * ε)) := by
              rw [hsqrt4]
      exact hs.symm
    have hmain : a / ε + Real.sqrt (b / ε) ≤ (N : ℝ) := by
      -- rewrite the bound hypothesis `hN` into the `a,b` notation
      have hab :
          a / ε + Real.sqrt (b / ε) =
            (4 * OperatorNormDef A' / ε) *
                Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) +
              2 * Real.sqrt (M * D1 / (σ1 * ε)) := by
        -- rewrite each term separately
        rw [hAop.symm, hB.symm]
      -- `hN` already has the right inequality direction (`≥`)
      have : (4 * OperatorNormDef A' / ε) *
              Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) +
                2 * Real.sqrt (M * D1 / (σ1 * ε)) ≤ (N : ℝ) := by
        simpa using hN
      simpa [hab] using this
    have hNle : (N : ℝ) ≤ (N : ℝ) + 1 := by
      exact le_add_of_nonneg_right (by norm_num)
    exact le_trans hmain hNle
  have hε_bound :=
    epsilon_bound_from_gap (a := a) (b := b) (ε := ε) (N := N) hε ha hb hN'
  have hgap_bound'' :
      f (ySeq N : E1) - φ hatu ≤ a / ((N : ℝ) + 1) + b / ((N : ℝ) + 1) ^ (2 : ℕ) := by
    have hrhs :
        (4 * OperatorNormDef A' / ((N : ℝ) + 1)) *
              Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)) +
            (4 * M * D1) / (σ1 * ((N : ℝ) + 1) ^ (2 : ℕ)) =
          a / ((N : ℝ) + 1) + b / ((N : ℝ) + 1) ^ (2 : ℕ) := by
      dsimp [a, b]
      rw [div_mul_eq_mul_div (4 * OperatorNormDef A') ((N : ℝ) + 1)
        (Real.sqrt (D1 * sSup (d2 '' Q2) / (σ1 * σ2)))]
      rw [div_mul_eq_div_div (4 * M * D1) σ1 (((N : ℝ) + 1) ^ (2 : ℕ))]
    exact le_trans hgap_bound' (le_of_eq hrhs)
  linarith [hgap_bound'', hε_bound]
