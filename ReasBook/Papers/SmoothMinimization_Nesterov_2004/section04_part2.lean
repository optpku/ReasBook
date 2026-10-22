/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section04_part1

open scoped NNReal

/-- Weighted linearization sum bound using the averaged dual point. -/
lemma weighted_sum_bound_hatu {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (fhat : E1 → ℝ) (phihat d2 : E2 → ℝ) (μ : ℝ)
    (uμ : E1 → E2) (A' : E1 →ₗ[ℝ] Module.Dual ℝ E2) (xSeq : ℕ → Q1) (N : ℕ) (hatu : Q2)
    (hhatudef :
      (hatu : E2) =
        Finset.sum (Finset.range (N + 1)) (fun i =>
          (2 * ((i : ℝ) + 1) / (((N : ℝ) + 1) * ((N : ℝ) + 2))) •
            uμ (xSeq i : E1)))
    (hQ1_open : IsOpen Q1) (hQ1_convex : Convex ℝ Q1)
    (hfhat_convex : ConvexOn ℝ Q1 fhat) (hfhat_diff : DifferentiableOn ℝ fhat Q1)
    (hfbar_diff :
      DifferentiableOn ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) Q1)
    (hphihat_convex : ConvexOn ℝ Q2 phihat)
    (hμ_nonneg : 0 ≤ μ) (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x))
    (hderivμ :
      ∀ x,
        fderiv ℝ (SmoothedMaxFunction Q2 A phihat d2 μ) x =
          (AdjointOperator A' (uμ x)).toContinuousLinearMap)
    (hpair : ∀ x u, DualPairing (AdjointOperator A' u) x = A x u) :
    ∀ x ∈ Q1,
      Finset.sum (Finset.range (N + 1)) (fun i =>
        ((i : ℝ) + 1) *
          (SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
            DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i))) ≤
        ((N : ℝ) + 1) * ((N : ℝ) + 2) / 2 *
          (fhat x + A x hatu - phihat hatu) := by
  classical
  intro x hx
  set fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
  have hfbar_diff' : DifferentiableOn ℝ (fun y => fhat y + fμ y) Q1 := by
    simpa [SmoothedObjective, fμ] using hfbar_diff
  have hfμ_diff : DifferentiableOn ℝ fμ Q1 := by
    have h := hfbar_diff'.sub hfhat_diff
    convert h using 1
    ext y
    simp [sub_eq_add_neg, add_assoc]
  have hfhat_diff_at : ∀ x ∈ Q1, DifferentiableAt ℝ fhat x := by
    intro x hx
    exact (hfhat_diff x hx).differentiableAt (hQ1_open.mem_nhds hx)
  have hfμ_diff_at : ∀ x ∈ Q1, DifferentiableAt ℝ fμ x := by
    intro x hx
    exact (hfμ_diff x hx).differentiableAt (hQ1_open.mem_nhds hx)
  have hderiv_add :
      ∀ x ∈ Q1,
        fderiv ℝ (fun y => fhat y + fμ y) x =
          fderiv ℝ fhat x + fderiv ℝ fμ x :=
    fderiv_add_on (s := Q1) (hf := hfhat_diff_at) (hg := hfμ_diff_at)
  have hderiv_add' :
      ∀ x ∈ Q1,
        fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) x =
          fderiv ℝ fhat x + fderiv ℝ fμ x := by
    intro x hx
    simpa [SmoothedObjective, fμ] using (hderiv_add x hx)
  set denom : ℝ := ((N : ℝ) + 1) * ((N : ℝ) + 2)
  have hdenom_pos : 0 < denom := by
    have h1 : 0 < (N : ℝ) + 1 := by nlinarith
    have h2 : 0 < (N : ℝ) + 2 := by nlinarith
    simpa [denom] using mul_pos h1 h2
  have hsum_w :
      Finset.sum (Finset.range (N + 1)) (fun i =>
        (2 * ((i : ℝ) + 1) / denom)) = (1 : ℝ) := by
    have hsum := sum_range_add_one_cast N
    have hterm :
        ∀ i, 2 * ((i : ℝ) + 1) / denom = (2 / denom) * ((i : ℝ) + 1) := by
      intro i
      simp [div_eq_mul_inv, mul_comm, mul_assoc]
    calc
      Finset.sum (Finset.range (N + 1)) (fun i => 2 * ((i : ℝ) + 1) / denom) =
          Finset.sum (Finset.range (N + 1)) (fun i => (2 / denom) * ((i : ℝ) + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hterm i]
      _ = (2 / denom) * Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1)) := by
            symm
            simpa using
              (Finset.mul_sum (s := Finset.range (N + 1)) (f := fun i => ((i : ℝ) + 1))
                (a := (2 / denom)))
      _ = (2 / denom) * (denom / 2) := by
            simp [hsum, denom]
      _ = (1 : ℝ) := by
            field_simp [denom, hdenom_pos.ne']
  have hnonneg_w :
      ∀ i ∈ Finset.range (N + 1), 0 ≤ 2 * ((i : ℝ) + 1) / denom := by
    intro i hi
    have hi' : 0 ≤ (i : ℝ) + 1 := by nlinarith
    have hnum : 0 ≤ 2 * ((i : ℝ) + 1) := by nlinarith
    exact div_nonneg hnum (le_of_lt hdenom_pos)
  have hmem_u :
      ∀ i ∈ Finset.range (N + 1), uμ (xSeq i : E1) ∈ Q2 := by
    intro i hi
    exact (hmax (xSeq i)).1
  have hphihat_jensen :
      phihat hatu ≤
        Finset.sum (Finset.range (N + 1)) (fun i =>
          (2 * ((i : ℝ) + 1) / denom) * phihat (uμ (xSeq i : E1))) := by
    have h :=
      ConvexOn.map_sum_le (t := Finset.range (N + 1)) (w := fun i =>
        2 * ((i : ℝ) + 1) / denom) (p := fun i => uμ (xSeq i : E1))
        hphihat_convex hnonneg_w hsum_w hmem_u
    simpa [hhatudef, smul_eq_mul, denom] using h
  have hphihat_sum :
      (denom / 2) * phihat hatu ≤
        Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) := by
    have hcoef_nonneg : 0 ≤ denom / 2 := by nlinarith [hdenom_pos]
    have hdenom_ne : denom ≠ 0 := by nlinarith [hdenom_pos]
    have hmul := mul_le_mul_of_nonneg_left hphihat_jensen hcoef_nonneg
    have hsum :
        (denom / 2) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              (2 * ((i : ℝ) + 1) / denom) * phihat (uμ (xSeq i : E1))) =
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) := by
      calc
        (denom / 2) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              (2 * ((i : ℝ) + 1) / denom) * phihat (uμ (xSeq i : E1))) =
            Finset.sum (Finset.range (N + 1)) (fun i =>
              (denom / 2) *
                ((2 * ((i : ℝ) + 1) / denom) * phihat (uμ (xSeq i : E1)))) := by
              simpa using
                (Finset.mul_sum (s := Finset.range (N + 1))
                  (f := fun i =>
                    (2 * ((i : ℝ) + 1) / denom) * phihat (uμ (xSeq i : E1)))
                  (a := denom / 2))
        _ =
            Finset.sum (Finset.range (N + 1)) (fun i =>
              ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [denom, hdenom_ne, mul_comm, mul_left_comm, mul_assoc]
    simpa [hsum] using hmul
  have hAx_hatu :
      A x hatu =
        Finset.sum (Finset.range (N + 1)) (fun i =>
          (2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1))) := by
    calc
      A x hatu =
          A x
            (Finset.sum (Finset.range (N + 1)) (fun i =>
              (2 * ((i : ℝ) + 1) / denom) • uμ (xSeq i : E1))) := by
            simp [hhatudef]
      _ =
          Finset.sum (Finset.range (N + 1)) (fun i =>
            (2 * ((i : ℝ) + 1) / denom) • A x (uμ (xSeq i : E1))) := by
            simp [map_sum, smul_eq_mul]
      _ =
          Finset.sum (Finset.range (N + 1)) (fun i =>
            (2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1))) := by
            simp [smul_eq_mul]
  have hAx_sum :
      Finset.sum (Finset.range (N + 1)) (fun i =>
        ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) =
        (denom / 2) * A x hatu := by
    have hdenom_ne : denom ≠ 0 := by nlinarith [hdenom_pos]
    calc
      Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) =
          (denom / 2) *
            Finset.sum (Finset.range (N + 1)) (fun i =>
              (2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1))) := by
            symm
            calc
              (denom / 2) *
                  Finset.sum (Finset.range (N + 1)) (fun i =>
                    (2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1))) =
                  Finset.sum (Finset.range (N + 1)) (fun i =>
                    (denom / 2) *
                      ((2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1)))) := by
                    simpa using
                      (Finset.mul_sum (s := Finset.range (N + 1))
                        (f := fun i =>
                          (2 * ((i : ℝ) + 1) / denom) * A x (uμ (xSeq i : E1)))
                        (a := denom / 2))
              _ =
                  Finset.sum (Finset.range (N + 1)) (fun i =>
                    ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    field_simp [denom, hdenom_ne, mul_comm, mul_left_comm, mul_assoc]
      _ = (denom / 2) * A x hatu := by
          simp [hAx_hatu]
  have hsum_fhat :
      Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1) * fhat x) =
        (denom / 2) * fhat x := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1) * fhat x) =
          Finset.sum (Finset.range (N + 1)) (fun i => fhat x * ((i : ℝ) + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [mul_comm]
      _ = (Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1))) * fhat x := by
            simpa [mul_comm] using (Finset.sum_mul (s := Finset.range (N + 1))
              (f := fun i => ((i : ℝ) + 1)) (a := fhat x)).symm
      _ = (denom / 2) * fhat x := by
            simp [sum_range_add_one_cast, denom]
  have hterm_le :
      ∀ i,
        SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
            DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i) ≤
          fhat x + A x (uμ (xSeq i : E1)) - phihat (uμ (xSeq i : E1)) := by
    intro i
    have hx_i : (xSeq i : E1) ∈ Q1 := (xSeq i).property
    have hderiv_i :
        fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i) =
          fderiv ℝ fhat (xSeq i) + fderiv ℝ fμ (xSeq i) := by
      exact hderiv_add' (xSeq i) hx_i
    have hhat_i :
        fhat x ≥
          fhat (xSeq i : E1) +
            DualPairing ((fderiv ℝ fhat (xSeq i)).toLinearMap) (x - xSeq i) := by
      have h :=
        convex_support_grad (hQ_open := hQ1_open) (hQ_convex := hQ1_convex)
          (hf_convex := hfhat_convex) (hf_diff := hfhat_diff) (u := x) (v := xSeq i)
          hx hx_i
      simpa using h
    have hμ_lin :
        fμ (xSeq i : E1) +
            DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (x - xSeq i) ≤
          A x (uμ (xSeq i : E1)) - phihat (uμ (xSeq i : E1)) := by
      have hlin0 :
          fμ (xSeq i : E1) -
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (xSeq i) =
            -phihat (uμ (xSeq i : E1)) - μ * d2 (uμ (xSeq i : E1)) := by
        have hlin :=
          smoothedMaxFunction_linearization (Q2 := Q2) (A := A) (phihat := phihat) (d2 := d2)
            (μ := μ) (uμ := uμ) (A' := A') (hmax := hmax) (hderiv := hderivμ) (hpair := hpair)
            (xSeq i : E1)
        simpa [fμ] using hlin
      have hderiv_lin :
          DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) x =
            A x (uμ (xSeq i : E1)) := by
        have h :=
          congrArg ContinuousLinearMap.toLinearMap (hderivμ (xSeq i))
        have h' := congrArg (fun T => T x) h
        have h'' :
            DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) x =
              DualPairing (AdjointOperator A' (uμ (xSeq i : E1))) x := by
          simpa [DualPairing, fμ] using h'
        simpa [hpair] using h''
      have hμd2_nonneg :
          0 ≤ μ * d2 (uμ (xSeq i : E1)) := by
        have hu : uμ (xSeq i : E1) ∈ Q2 := (hmax (xSeq i)).1
        exact mul_nonneg hμ_nonneg (hd2_nonneg _ hu)
      have hsub :
          DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (x - xSeq i) =
            DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) x -
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (xSeq i) := by
        simp [DualPairing, map_sub]
      calc
        fμ (xSeq i : E1) +
            DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (x - xSeq i) =
            (fμ (xSeq i : E1) -
                DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (xSeq i)) +
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) x := by
          simp [hsub]
          ring
        _ =
            (-phihat (uμ (xSeq i : E1)) - μ * d2 (uμ (xSeq i : E1))) +
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) x := by
          simp [hlin0]
        _ =
            (-phihat (uμ (xSeq i : E1)) - μ * d2 (uμ (xSeq i : E1))) +
              A x (uμ (xSeq i : E1)) := by
          simp [hderiv_lin]
        _ ≤ A x (uμ (xSeq i : E1)) - phihat (uμ (xSeq i : E1)) := by
          linarith [hμd2_nonneg]
    have hsplit :
        SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
            DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i) =
          (fhat (xSeq i : E1) +
              DualPairing ((fderiv ℝ fhat (xSeq i)).toLinearMap) (x - xSeq i)) +
            (fμ (xSeq i : E1) +
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (x - xSeq i)) := by
      have hpair' :
          DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i) =
            DualPairing ((fderiv ℝ fhat (xSeq i)).toLinearMap) (x - xSeq i) +
              DualPairing ((fderiv ℝ fμ (xSeq i)).toLinearMap) (x - xSeq i) := by
        simp [hderiv_i, DualPairing]
      simp [SmoothedObjective, fμ, hpair']
      ring
    have hsum := add_le_add hhat_i hμ_lin
    linarith [hsum, hsplit]
  have hsum_term :
      Finset.sum (Finset.range (N + 1)) (fun i =>
        ((i : ℝ) + 1) *
          (SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
            DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i))) ≤
        Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) * (fhat x + A x (uμ (xSeq i : E1)) - phihat (uμ (xSeq i : E1)))) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hnonneg : 0 ≤ (i : ℝ) + 1 := by nlinarith
    exact mul_le_mul_of_nonneg_left (hterm_le i) hnonneg
  have hsum_rhs :
      Finset.sum (Finset.range (N + 1)) (fun i =>
        ((i : ℝ) + 1) * (fhat x + A x (uμ (xSeq i : E1)) - phihat (uμ (xSeq i : E1)))) =
        (denom / 2) * fhat x +
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) -
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) := by
    simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_fhat]
  have hfinal_rhs :
      (denom / 2) * fhat x +
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) -
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) ≤
        (denom / 2) * (fhat x + A x hatu - phihat hatu) := by
    have hphihat_sum' :
        -Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) ≤ -(denom / 2) * phihat hatu := by
      linarith [hphihat_sum]
    have hAx_sum' :
        Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) = (denom / 2) * A x hatu := hAx_sum
    have hsum_fhat' :
        Finset.sum (Finset.range (N + 1)) (fun i => ((i : ℝ) + 1) * fhat x) =
          (denom / 2) * fhat x := hsum_fhat
    linarith [hAx_sum', hsum_fhat', hphihat_sum']
  calc
    Finset.sum (Finset.range (N + 1)) (fun i =>
        ((i : ℝ) + 1) *
          (SmoothedObjective Q2 A phihat d2 μ fhat (xSeq i : E1) +
            DualPairing
              ((fderiv ℝ (SmoothedObjective Q2 A phihat d2 μ fhat) (xSeq i)).toLinearMap)
              (x - xSeq i))) ≤
        Finset.sum (Finset.range (N + 1)) (fun i =>
          ((i : ℝ) + 1) *
            (fhat x +
              A x (uμ (xSeq i : E1)) -
              phihat (uμ (xSeq i : E1)))) := hsum_term
    _ =
        (denom / 2) * fhat x +
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * A x (uμ (xSeq i : E1))) -
          Finset.sum (Finset.range (N + 1)) (fun i =>
            ((i : ℝ) + 1) * phihat (uμ (xSeq i : E1))) := hsum_rhs
    _ ≤ (denom / 2) * (fhat x + A x hatu - phihat hatu) := hfinal_rhs

/-- If `μ` is chosen as in the smoothing rule, its square satisfies the scaling identity. -/
lemma mu_sq_identity (D1 D2 σ1 σ2 μ Aop : ℝ) (N : ℕ)
    (hμ_def : μ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2)))
    (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hD2ne : D2 ≠ 0) :
    μ ^ 2 * (σ1 * σ2 * D2) * ((N : ℝ) + 1) ^ 2 = 4 * Aop ^ 2 * D1 := by
  have hdenom_nonneg : 0 ≤ σ1 * σ2 * D2 := by
    have hσ1_nonneg : 0 ≤ σ1 := le_of_lt hσ1
    have hσ2_nonneg : 0 ≤ σ2 := le_of_lt hσ2
    have hσ12_nonneg : 0 ≤ σ1 * σ2 := mul_nonneg hσ1_nonneg hσ2_nonneg
    exact mul_nonneg hσ12_nonneg hD2
  have hnonneg : 0 ≤ D1 / (σ1 * σ2 * D2) := by
    exact div_nonneg hD1 hdenom_nonneg
  have hμ_sq : μ ^ 2 = (2 * Aop / ((N : ℝ) + 1)) ^ 2 * (D1 / (σ1 * σ2 * D2)) := by
    calc
      μ ^ 2 = ((2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2))) ^ 2 := by
        simp [hμ_def]
      _ = (2 * Aop / ((N : ℝ) + 1)) ^ 2 * (Real.sqrt (D1 / (σ1 * σ2 * D2))) ^ 2 := by
        ring
      _ = (2 * Aop / ((N : ℝ) + 1)) ^ 2 * (D1 / (σ1 * σ2 * D2)) := by
        simp [Real.sq_sqrt hnonneg]
  have hσ1ne : σ1 ≠ 0 := ne_of_gt hσ1
  have hσ2ne : σ2 ≠ 0 := ne_of_gt hσ2
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := by nlinarith
  field_simp [hσ1ne, hσ2ne, hD2ne, hN1ne] at hμ_sq
  nlinarith [hμ_sq]

/-- If `μ` is chosen as in the smoothing rule, then `μ * D2` simplifies to the sqrt expression. -/
lemma mu_mul_D2_sqrt (D1 D2 σ1 σ2 μ Aop : ℝ) (N : ℕ)
    (hμ_def : μ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2)))
    (hD2 : 0 ≤ D2) (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) :
    μ * D2 = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
  by_cases hD2zero : D2 = 0
  · simp [hμ_def, hD2zero]
  · have hσ1ne : σ1 ≠ 0 := ne_of_gt hσ1
    have hσ2ne : σ2 ≠ 0 := ne_of_gt hσ2
    have hD2ne : D2 ≠ 0 := hD2zero
    have hsqrt : Real.sqrt (D2 * D2) = D2 := by
      simpa using (Real.sqrt_mul_self hD2)
    have hmul : D1 / (σ1 * σ2 * D2) * (D2 * D2) = D1 * D2 / (σ1 * σ2) := by
      field_simp [hD2ne, hσ1ne, hσ2ne]
    have hmul_sqrt :
        Real.sqrt (D1 / (σ1 * σ2 * D2)) * Real.sqrt (D2 * D2) =
          Real.sqrt (D1 / (σ1 * σ2 * D2) * (D2 * D2)) := by
      have hnonneg : 0 ≤ D2 * D2 := mul_nonneg hD2 hD2
      have h := (Real.sqrt_mul' (x := D1 / (σ1 * σ2 * D2)) (hy := hnonneg))
      simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
    have hcalc :
        Real.sqrt (D1 / (σ1 * σ2 * D2)) * D2 =
          Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
      calc
        Real.sqrt (D1 / (σ1 * σ2 * D2)) * D2
            = Real.sqrt (D1 / (σ1 * σ2 * D2)) * Real.sqrt (D2 * D2) := by
                simp [hsqrt]
        _ = Real.sqrt (D1 / (σ1 * σ2 * D2) * (D2 * D2)) := by
                simpa using hmul_sqrt
        _ = Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
                simp [hmul]
    calc
      μ * D2 = (2 * Aop / ((N : ℝ) + 1)) * (Real.sqrt (D1 / (σ1 * σ2 * D2)) * D2) := by
        simp [hμ_def, mul_left_comm, mul_comm]
      _ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
        simp [hcalc]

/-- The inverse-`μ` term equals `μ * D2` scaled by `(N+1)/(N+2)`. -/
lemma mu_inv_term_eq (D1 D2 σ1 σ2 μ Aop : ℝ) (N : ℕ)
    (hμ_def : μ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2)))
    (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hμ : μ ≠ 0) :
    (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
        (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) =
      μ * D2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  have hD2ne : D2 ≠ 0 := by
    intro hD2zero
    apply hμ
    simp [hμ_def, hD2zero]
  have hμ_sq' := mu_sq_identity (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ)
    (Aop := Aop) (N := N) hμ_def hσ1 hσ2 hD1 hD2 hD2ne
  have hσ1ne : σ1 ≠ 0 := ne_of_gt hσ1
  have hσ2ne : σ2 ≠ 0 := ne_of_gt hσ2
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := by nlinarith
  have hN2ne : ((N : ℝ) + 2) ≠ 0 := by nlinarith
  field_simp [hμ, hσ1ne, hσ2ne, hN1ne, hN2ne]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hμ_sq'.symm

/-- The inverse-`μ` term is bounded by the sqrt expression. -/
lemma mu_inv_term_le (D1 D2 σ1 σ2 μ Aop : ℝ) (N : ℕ)
    (hμ_def : μ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2)))
    (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hAop : 0 ≤ Aop) :
    (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
        (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
      (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
  by_cases hμ : μ = 0
  · have hNpos : 0 < (N : ℝ) + 1 := by nlinarith
    have hfrac_nonneg : 0 ≤ (2 * Aop) / ((N : ℝ) + 1) := by
      exact div_nonneg (by nlinarith [hAop]) (le_of_lt hNpos)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
      exact Real.sqrt_nonneg _
    have hRHS_nonneg : 0 ≤ (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
      exact mul_nonneg hfrac_nonneg hsqrt_nonneg
    simpa [hμ] using hRHS_nonneg
  · have hμterm_eq :=
        mu_inv_term_eq (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ) (Aop := Aop)
          (N := N) hμ_def hσ1 hσ2 hD1 hD2 hμ
    have hratio_le : ((N : ℝ) + 1) / ((N : ℝ) + 2) ≤ (1 : ℝ) := by
      have hN2pos : 0 < (N : ℝ) + 2 := by nlinarith
      exact (div_le_one hN2pos).2 (by nlinarith)
    have hμ_nonneg : 0 ≤ μ := by
      have hNpos : 0 < (N : ℝ) + 1 := by nlinarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt (D1 / (σ1 * σ2 * D2)) := by
        exact Real.sqrt_nonneg _
      have hfrac_nonneg : 0 ≤ (2 * Aop) / ((N : ℝ) + 1) := by
        exact div_nonneg (by nlinarith [hAop]) (le_of_lt hNpos)
      simpa [hμ_def] using mul_nonneg hfrac_nonneg hsqrt_nonneg
    have hμD2_nonneg : 0 ≤ μ * D2 := by
      exact mul_nonneg hμ_nonneg hD2
    have hscale_le : μ * D2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) ≤ μ * D2 := by
      have hle := mul_le_mul_of_nonneg_left hratio_le hμD2_nonneg
      simpa [mul_assoc] using hle
    have hμD2 :=
      mu_mul_D2_sqrt (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ) (Aop := Aop)
        (N := N) hμ_def hD2 hσ1 hσ2
    calc
      (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
          (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) =
          μ * D2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) := by
            simpa [div_eq_mul_inv, mul_assoc] using hμterm_eq
      _ ≤ μ * D2 := hscale_le
      _ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
            simpa using hμD2

/-- Simplify the `μ`-dependent terms in the gap bound. -/
lemma mu_simplify_bound (D1 D2 σ1 σ2 μ : ℝ) (N : ℕ) (Aop : ℝ)
    (hμ_def : μ = (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 / (σ1 * σ2 * D2)))
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hAop : 0 ≤ Aop) :
    μ * D2 +
        (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
          (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
      (4 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
  have hμD2 :=
    mu_mul_D2_sqrt (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ) (Aop := Aop)
      (N := N) hμ_def hD2 hσ1 hσ2
  have hμinv :=
    mu_inv_term_le (D1 := D1) (D2 := D2) (σ1 := σ1) (σ2 := σ2) (μ := μ) (Aop := Aop)
      (N := N) hμ_def hσ1 hσ2 hD1 hD2 hAop
  have hsum :
      μ * D2 +
          (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
            (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
        (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) +
          (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
    linarith [hμD2, hμinv]
  calc
    μ * D2 +
        (4 * (1 / (μ * σ2)) * Aop ^ 2 * D1) /
          (σ1 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
        (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) +
          (2 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := hsum
    _ = (4 * Aop / ((N : ℝ) + 1)) * Real.sqrt (D1 * D2 / (σ1 * σ2)) := by
        ring

/-- Convert an iteration lower bound to an ε-accuracy bound. -/
lemma epsilon_bound_from_gap {a b ε : ℝ} {N : ℕ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN : (N : ℝ) + 1 ≥ a / ε + Real.sqrt (b / ε)) :
    a / ((N : ℝ) + 1) + b / ((N : ℝ) + 1) ^ (2 : ℕ) ≤ ε := by
  set t : ℝ := (N : ℝ) + 1 with ht_def
  have htpos : 0 < t := by
    have htpos' : 0 < (N : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_pos N)
    simpa [ht_def] using htpos'
  have htne : t ≠ 0 := ne_of_gt htpos
  set s : ℝ := t - a / ε with hs_def
  have hs : Real.sqrt (b / ε) ≤ s := by
    have hN' : a / ε + Real.sqrt (b / ε) ≤ t := by simpa [ht_def] using hN
    linarith [hN']
  have hs_nonneg : 0 ≤ s := le_trans (Real.sqrt_nonneg _) hs
  have hbε_nonneg : 0 ≤ b / ε := div_nonneg hb (le_of_lt hε)
  have hb_le : b ≤ ε * s ^ (2 : ℕ) := by
    have hsq : (Real.sqrt (b / ε)) ^ (2 : ℕ) ≤ s ^ (2 : ℕ) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (b / ε) := Real.sqrt_nonneg _
      have hmul := mul_le_mul hs hs hsqrt_nonneg hs_nonneg
      simpa [pow_two] using hmul
    have hsq' : b / ε ≤ s ^ (2 : ℕ) := by
      simpa [Real.sq_sqrt hbε_nonneg] using hsq
    have hmul := mul_le_mul_of_nonneg_left hsq' (le_of_lt hε)
    simpa [div_eq_mul_inv, hε.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
  have hb_le' : b ≤ a * s + ε * s ^ (2 : ℕ) := by
    have has_nonneg : 0 ≤ a * s := mul_nonneg ha hs_nonneg
    linarith [hb_le, has_nonneg]
  have ht_as : t = a / ε + s := by simp [hs_def]
  have hineq : a * t + b ≤ ε * t ^ (2 : ℕ) := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    calc
      a * t + b ≤ a * t + (a * s + ε * s ^ (2 : ℕ)) := by
        have h := add_le_add_left hb_le' (a * t)
        simpa [add_assoc, add_left_comm, add_comm] using h
      _ = a * (a / ε + s) + (a * s + ε * s ^ (2 : ℕ)) := by simp [ht_as]
      _ = ε * (a / ε + s) ^ (2 : ℕ) := by
        -- clear the single denominator `ε` and expand
        field_simp [hεne, pow_two]
      _ = ε * t ^ (2 : ℕ) := by simp [ht_as]
  have ht2pos : 0 < t ^ (2 : ℕ) := by
    simpa using (pow_pos htpos 2)
  have hcalc : a / t + b / t ^ (2 : ℕ) = (a * t + b) / t ^ (2 : ℕ) := by
    field_simp [htne, pow_two]
  have hineq' : (a * t + b) / t ^ (2 : ℕ) ≤ ε := by
    exact (div_le_iff₀ ht2pos).2 hineq
  have hfinal : a / t + b / t ^ (2 : ℕ) ≤ ε := by
    calc
      a / t + b / t ^ (2 : ℕ) = (a * t + b) / t ^ (2 : ℕ) := hcalc
      _ ≤ ε := hineq'
  -- rewrite in terms of `t = (N:ℝ) + 1`
  simpa [ht_def] using hfinal
