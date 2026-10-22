/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section05_part2

open scoped BigOperators Topology

open Filter

/-- After the min-max exchange, the inner simplex minimization equals the minimum coefficient. -/
lemma simplexProximalValue_dual_after_exchange (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hxbar : xbar ∈ standardSimplex n) (hL : 0 < L) :
    simplexProximalValue n xbar gbar L =
      sSup
        ((fun s : Fin n → ℝ =>
              (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
          (Set.univ : Set (Fin n → ℝ))) := by
  classical
  have hminimax :=
    simplexProximalValue_as_minimax_fin (n := n) (xbar := xbar) (gbar := gbar) (L := L) hL
  have hswap :=
    simplexProximalValue_minmax_exchange_fin (n := n) (xbar := xbar) (gbar := gbar) (L := L) hL
  have hswap' :
      simplexProximalValue n xbar gbar L =
        sSup
          ((fun s : Fin n → ℝ =>
                sInf
                  ((fun x : Fin n → ℝ =>
                        (∑ i, (gbar i + s i) * (x i - xbar i)) -
                          (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
            (Set.univ : Set (Fin n → ℝ))) := by
    calc
      simplexProximalValue n xbar gbar L =
          sInf
            ((fun x =>
                  sSup
                    ((fun s : Fin n → ℝ =>
                          (∑ i, (gbar i + s i) * (x i - xbar i)) -
                            (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
                      (Set.univ : Set (Fin n → ℝ)))) '' standardSimplex n) := hminimax
      _ =
          sSup
            ((fun s : Fin n → ℝ =>
                  sInf
                    ((fun x : Fin n → ℝ =>
                          (∑ i, (gbar i + s i) * (x i - xbar i)) -
                            (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
              (Set.univ : Set (Fin n → ℝ))) := hswap
  have hpoint :
      ∀ s : Fin n → ℝ,
        sInf
            ((fun x : Fin n → ℝ =>
                  (∑ i, (gbar i + s i) * (x i - xbar i)) -
                    (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n) =
          (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
            sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n))) := by
    intro s
    let r : Fin n → ℝ := fun i => gbar i + s i
    have hsum : ∀ x : Fin n → ℝ,
        ∑ i, r i * (x i - xbar i) = (∑ i, r i * x i) - ∑ i, r i * xbar i := by
      intro x
      calc
        ∑ i, r i * (x i - xbar i) = ∑ i, (r i * x i - r i * xbar i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = (∑ i, r i * x i) - ∑ i, r i * xbar i := by
          simp [Finset.sum_sub_distrib]
    let c : ℝ := (-∑ i, r i * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)
    have hrewrite :
        ∀ x : Fin n → ℝ,
          c + ∑ i, r i * x i =
            (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
      intro x
      calc
        c + ∑ i, r i * x i =
            (-∑ i, r i * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) + ∑ i, r i * x i := by
              rfl
        _ = (∑ i, r i * x i) - ∑ i, r i * xbar i - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              ring
        _ = (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) := by
              simp [hsum x]
    have hset :
        ((fun x : Fin n → ℝ =>
              (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
            standardSimplex n) =
          ((fun x : Fin n → ℝ => c + ∑ i, r i * x i) '' standardSimplex n) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        exact hrewrite x
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        exact (hrewrite x).symm
    have hbd :
        BddBelow ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) := by
      refine ⟨sInf (r '' (Set.univ : Set (Fin n))), ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hle := sInf_coeff_le_linear_standardSimplex (r := r) x hx
      simpa using hle
    have hne : ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n).Nonempty := by
      refine ⟨∑ i, r i * xbar i, ?_⟩
      exact ⟨xbar, hxbar, rfl⟩
    have hshift :
        sInf ((fun x : Fin n → ℝ => c + ∑ i, r i * x i) '' standardSimplex n) =
          c + sInf ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) := by
      have hcomp :
          (fun x => c + x) '' ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) =
            (fun x : Fin n → ℝ => c + ∑ i, r i * x i) '' standardSimplex n := by
        simp [Set.image_image]
      have hshift' :=
        sInf_image_add_const (a := c)
          (s := (fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) hbd hne
      simpa [hcomp] using hshift'
    calc
      sInf
          ((fun x : Fin n → ℝ =>
                (∑ i, r i * (x i - xbar i)) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) ''
            standardSimplex n)
          = sInf ((fun x : Fin n → ℝ => c + ∑ i, r i * x i) '' standardSimplex n) := by
              rw [hset]
      _ = c + sInf ((fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n) := hshift
      _ = c + sInf ((fun i => r i) '' (Set.univ : Set (Fin n))) := by
            simpa using (dual_inner_min_over_simplex (n := n) (r := r))
      _ =
          (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
            sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n))) := by
            simp [c, r, sub_eq_add_neg, add_comm]
  have himage :
      ((fun s : Fin n → ℝ =>
            sInf
              ((fun x : Fin n → ℝ =>
                    (∑ i, (gbar i + s i) * (x i - xbar i)) -
                      (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
          (Set.univ : Set (Fin n → ℝ))) =
        ((fun s : Fin n → ℝ =>
              (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
          (Set.univ : Set (Fin n → ℝ))) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simpa [Set.image_univ] using (hpoint s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simpa [Set.image_univ] using (hpoint s)⟩
  calc
    simplexProximalValue n xbar gbar L =
        sSup
          ((fun s : Fin n → ℝ =>
                sInf
                  ((fun x : Fin n → ℝ =>
                        (∑ i, (gbar i + s i) * (x i - xbar i)) -
                          (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ)) '' standardSimplex n)) ''
            (Set.univ : Set (Fin n → ℝ))) := hswap'
    _ =
        sSup
          ((fun s : Fin n → ℝ =>
                (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                  sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
            (Set.univ : Set (Fin n → ℝ))) := by
              rw [himage]

/-- Normalization on a finite index set yields a zero coordinate. -/
lemma simplexProximalValue_exists_zero_coord (n : ℕ) (gbar : Fin n → ℝ) (hn : 0 < n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) :
    ∃ i0, gbar i0 = 0 := by
  classical
  let S : Set ℝ := (fun i => gbar i) '' (Set.univ : Set (Fin n))
  have hfin : S.Finite := (Set.finite_univ.image fun i => gbar i)
  have hne : S.Nonempty := by
    refine ⟨gbar ⟨0, hn⟩, ?_⟩
    exact ⟨⟨0, hn⟩, by simp, rfl⟩
  have hmem : (sInf S) ∈ S := Set.Nonempty.csInf_mem hne hfin
  have hmin' : sInf S = 0 := by
    simpa [S] using hmin
  have hmem' : (0 : ℝ) ∈ S := by
    simpa [hmin'] using hmem
  rcases hmem' with ⟨i0, hi0, hgi0⟩
  exact ⟨i0, by simpa using hgi0⟩

/-- Normalization implies nonnegativity of all coordinates. -/
lemma simplexProximalValue_gbar_nonneg (n : ℕ) (gbar : Fin n → ℝ)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) :
    ∀ i, 0 ≤ gbar i := by
  intro i
  have hmem : gbar i ∈ ((fun i => gbar i) '' (Set.univ : Set (Fin n))) := by
    exact ⟨i, by simp, rfl⟩
  have hbdd : BddBelow ((fun i => gbar i) '' (Set.univ : Set (Fin n))) := by
    exact (Set.finite_univ.image fun i => gbar i).bddBelow
  have hle : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) ≤ gbar i :=
    csInf_le hbdd hmem
  have hmin' : sInf (Set.range fun i => gbar i) = 0 := by
    simpa using hmin
  simpa [hmin'] using hle

/-- Shifting inside a `max` yields a positive-part expression. -/
lemma max_sub_eq (a b : ℝ) : max a b - a = max (b - a) 0 := by
  by_cases h : a ≤ b
  · have hb : max a b = b := max_eq_right h
    have hba : 0 ≤ b - a := by linarith
    simp [hb, hba]
  · have h' : b ≤ a := le_of_not_ge h
    have hb : max a b = a := max_eq_left h'
    have hba : b - a ≤ 0 := by linarith
    have hmax : max (b - a) 0 = 0 := max_eq_right hba
    simp [hb, hmax]

/-- If `λ ≤ τ`, the shifted `max` dominates the `2τ` truncation. -/
lemma max_sub_ge_of_le (lam τ g : ℝ) (hlam : lam ≤ τ) :
    max lam (g - τ) - lam ≥ max (g - (2 : ℝ) * τ) 0 := by
  have hle : g - (2 : ℝ) * τ ≤ g - τ - lam := by linarith [hlam]
  have hmax : max (g - (2 : ℝ) * τ) 0 ≤ max (g - τ - lam) 0 :=
    max_le_max hle le_rfl
  have hrewrite : max lam (g - τ) - lam = max (g - τ - lam) 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (max_sub_eq lam (g - τ))
  simpa [hrewrite] using hmax

/-- Lower bound the dual objective by the `τ`-reduced expression. -/
lemma simplexProximalValue_dual_reduce_to_tau_lower_bound (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hn : 0 < n) (hxbar : xbar ∈ standardSimplex n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) (s : Fin n → ℝ) :
    (∑ i, s i * xbar i) + (1 / (2 * L)) * ‖s - gbar‖ ^ (2 : ℕ) -
        sInf ((fun i => s i) '' (Set.univ : Set (Fin n))) ≥
      (∑ i, xbar i * max (gbar i - (2 : ℝ) * ‖s - gbar‖) 0) +
        (‖s - gbar‖ ^ (2 : ℕ)) / (2 * L) := by
  classical
  set τ : ℝ := ‖s - gbar‖ with hτdef
  set lam : ℝ := sInf ((fun i => s i) '' (Set.univ : Set (Fin n))) with hlamdef
  have hbdd_s : BddBelow ((fun i => s i) '' (Set.univ : Set (Fin n))) := by
    exact (Set.finite_univ.image fun i => s i).bddBelow
  have hτ : 0 ≤ τ := by exact norm_nonneg _
  have hxbar_nonneg : ∀ i, 0 ≤ xbar i := hxbar.1
  have hsum_le :
      ∑ i, xbar i * max lam (gbar i - τ) ≤ ∑ i, xbar i * s i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hlam_i : lam ≤ s i := csInf_le hbdd_s ⟨i, by simp, rfl⟩
    have hnorm_i : |s i - gbar i| ≤ τ := by
      simpa [τ] using (norm_le_pi_norm (f := s - gbar) i)
    have hdiff : gbar i - τ ≤ s i := by
      have hle := (abs_le.mp hnorm_i).1
      linarith
    have hmax_le : max lam (gbar i - τ) ≤ s i := max_le_iff.mpr ⟨hlam_i, hdiff⟩
    exact mul_le_mul_of_nonneg_left hmax_le (hxbar_nonneg i)
  have hsum_ge :
      ∑ i, s i * xbar i ≥ ∑ i, xbar i * max lam (gbar i - τ) := by
    simpa [mul_comm] using hsum_le
  rcases simplexProximalValue_exists_zero_coord (n := n) (gbar := gbar) hn hmin with ⟨i0, hi0⟩
  have hlam_le : lam ≤ s i0 := csInf_le hbdd_s ⟨i0, by simp, rfl⟩
  have hnorm0 : |s i0 - gbar i0| ≤ τ := by
    simpa [τ] using (norm_le_pi_norm (f := s - gbar) i0)
  have hlam_leτ : lam ≤ τ := by
    have hsi0_le : s i0 ≤ |s i0| := le_abs_self _
    have habs : |s i0| ≤ τ := by simpa [hi0] using hnorm0
    exact le_trans hlam_le (hsi0_le.trans habs)
  have hsum_shift :
      ∑ i, xbar i * max lam (gbar i - τ) - lam =
        ∑ i, xbar i * (max lam (gbar i - τ) - lam) := by
    calc
      ∑ i, xbar i * max lam (gbar i - τ) - lam
          = ∑ i, xbar i * max lam (gbar i - τ) - lam * ∑ i, xbar i := by
              simp [hxbar.2]
      _ = ∑ i, xbar i * max lam (gbar i - τ) - ∑ i, xbar i * lam := by
              have hmul :
                  lam * ∑ i, xbar i = ∑ i, xbar i * lam := by
                calc
                  lam * ∑ i, xbar i = ∑ i, lam * xbar i := by
                    simp [Finset.mul_sum]
                  _ = ∑ i, xbar i * lam := by
                    simp [mul_comm]
              simp [hmul]
      _ = ∑ i, (xbar i * max lam (gbar i - τ) - xbar i * lam) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ i, xbar i * (max lam (gbar i - τ) - lam) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hsum_le' :
      ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 ≤
        ∑ i, xbar i * (max lam (gbar i - τ) - lam) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hmax :
        max (gbar i - (2 : ℝ) * τ) 0 ≤ max lam (gbar i - τ) - lam := by
      exact (max_sub_ge_of_le (lam := lam) (τ := τ) (g := gbar i) hlam_leτ)
    exact mul_le_mul_of_nonneg_left hmax (hxbar_nonneg i)
  have hsum_ge' :
      ∑ i, xbar i * max lam (gbar i - τ) - lam ≥
        ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 := by
    have hsum_le'' :
        ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 ≤
          ∑ i, xbar i * max lam (gbar i - τ) - lam := by
      simpa [hsum_shift] using hsum_le'
    exact hsum_le''
  have hmain :
      (∑ i, s i * xbar i) + (1 / (2 * L)) * τ ^ (2 : ℕ) - lam ≥
        (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (1 / (2 * L)) * τ ^ (2 : ℕ) := by
    calc
      (∑ i, s i * xbar i) + (1 / (2 * L)) * τ ^ (2 : ℕ) - lam
          ≥ (∑ i, xbar i * max lam (gbar i - τ)) + (1 / (2 * L)) * τ ^ (2 : ℕ) - lam := by
              linarith [hsum_ge]
      _ ≥ (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (1 / (2 * L)) * τ ^ (2 : ℕ) := by
            linarith [hsum_ge']
  simpa [hτdef, hlamdef, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain

/-- Construct a dual variable achieving the `τ`-reduction. -/
lemma simplexProximalValue_dual_reduce_to_tau_construct (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hn : 0 < n) (hxbar : xbar ∈ standardSimplex n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) :
    ∀ {τ : ℝ}, 0 ≤ τ →
      ∃ s : Fin n → ℝ,
        (∑ i, s i * xbar i) + (1 / (2 * L)) * ‖s - gbar‖ ^ (2 : ℕ) -
            sInf ((fun i => s i) '' (Set.univ : Set (Fin n))) =
          (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (τ ^ (2 : ℕ)) / (2 * L) := by
  classical
  intro τ hτ
  rcases simplexProximalValue_exists_zero_coord (n := n) (gbar := gbar) hn hmin with ⟨i0, hi0⟩
  let sτ : Fin n → ℝ := fun i => max τ (gbar i - τ)
  have hxbar_nonneg : ∀ i, 0 ≤ xbar i := hxbar.1
  have hnorm_le : ‖sτ - gbar‖ ≤ τ := by
    refine (pi_norm_le_iff_of_nonneg hτ).2 ?_
    intro i
    by_cases hgi : gbar i ≤ (2 : ℝ) * τ
    · have hmax : sτ i = τ := by
        have : gbar i - τ ≤ τ := by linarith
        simp [sτ, max_eq_left this]
      have hnonneg : 0 ≤ gbar i := simplexProximalValue_gbar_nonneg (n := n) (gbar := gbar) hmin i
      have hbound : |τ - gbar i| ≤ τ := by
        refine (abs_le.mpr ?_)
        constructor <;> linarith
      simpa [sτ, hmax] using hbound
    · have hmax : sτ i = gbar i - τ := by
        have : τ ≤ gbar i - τ := by linarith
        simp [sτ, max_eq_right this]
      have habs : |sτ i - gbar i| = τ := by
        calc
          |sτ i - gbar i| = |(gbar i - τ) - gbar i| := by
            simp [sτ, hmax]
          _ = |-τ| := by
            have hdiff : (gbar i - τ) - gbar i = -τ := by ring
            simp [hdiff]
          _ = |τ| := by simp
          _ = τ := by simp [abs_of_nonneg hτ]
      simpa using (le_of_eq habs)
  have hnorm_ge : τ ≤ ‖sτ - gbar‖ := by
    have hcoord : |sτ i0 - gbar i0| = τ := by
      have hmax : sτ i0 = τ := by
        have : gbar i0 - τ ≤ τ := by linarith [hτ, hi0]
        simp [sτ, max_eq_left this]
      simp [hmax, hi0, abs_of_nonneg hτ]
    have hle : |sτ i0 - gbar i0| ≤ ‖sτ - gbar‖ := by
      simpa using (norm_le_pi_norm (f := sτ - gbar) i0)
    simpa [hcoord] using hle
  have hnorm : ‖sτ - gbar‖ = τ := le_antisymm hnorm_le hnorm_ge
  have hbdd_sτ : BddBelow ((fun i => sτ i) '' (Set.univ : Set (Fin n))) := by
    exact (Set.finite_univ.image fun i => sτ i).bddBelow
  have hInf_le : sInf ((fun i => sτ i) '' (Set.univ : Set (Fin n))) ≤ τ := by
    have hmem : sτ i0 ∈ ((fun i => sτ i) '' (Set.univ : Set (Fin n))) := by
      exact ⟨i0, by simp, rfl⟩
    have hle : sInf ((fun i => sτ i) '' (Set.univ : Set (Fin n))) ≤ sτ i0 :=
      csInf_le hbdd_sτ hmem
    have hval : sτ i0 = τ := by
      have : gbar i0 - τ ≤ τ := by linarith [hτ, hi0]
      simp [sτ, max_eq_left this]
    simpa [hval] using hle
  have hInf_ge : τ ≤ sInf ((fun i => sτ i) '' (Set.univ : Set (Fin n))) := by
    have hbound : ∀ y ∈ ((fun i => sτ i) '' (Set.univ : Set (Fin n))), τ ≤ y := by
      intro y hy
      rcases hy with ⟨i, hi, rfl⟩
      exact le_max_left _ _
    have hne : ((fun i => sτ i) '' (Set.univ : Set (Fin n))).Nonempty := by
      exact ⟨sτ i0, ⟨i0, by simp, rfl⟩⟩
    exact le_csInf hne hbound
  have hInf : sInf ((fun i => sτ i) '' (Set.univ : Set (Fin n))) = τ :=
    le_antisymm hInf_le hInf_ge
  have hInf' : sInf (Set.range fun i => sτ i) = τ := by
    simpa using hInf
  have hsum_shift :
      ∑ i, sτ i * xbar i - τ = ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 := by
    calc
      ∑ i, sτ i * xbar i - τ
          = ∑ i, xbar i * sτ i - τ := by
              simp [mul_comm]
      _ = ∑ i, xbar i * sτ i - τ * ∑ i, xbar i := by
            simp [hxbar.2]
      _ = ∑ i, xbar i * sτ i - ∑ i, xbar i * τ := by
            have hmul :
                τ * ∑ i, xbar i = ∑ i, xbar i * τ := by
              simp [Finset.mul_sum, mul_comm]
            simp [hmul]
      _ = ∑ i, (xbar i * sτ i - xbar i * τ) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ i, xbar i * (sτ i - τ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hrewrite :
                sτ i - τ = max (gbar i - (2 : ℝ) * τ) 0 := by
              have htmp : max τ (gbar i - τ) - τ = max (gbar i - (2 : ℝ) * τ) 0 := by
                have htmp' : max τ (gbar i - τ) - τ = max ((gbar i - τ) - τ) 0 := by
                  simpa using (max_sub_eq τ (gbar i - τ))
                calc
                  max τ (gbar i - τ) - τ = max ((gbar i - τ) - τ) 0 := htmp'
                  _ = max (gbar i - (2 : ℝ) * τ) 0 := by ring_nf
              simp [sτ, htmp]
            simp [hrewrite]
  refine ⟨sτ, ?_⟩
  calc
    (∑ i, sτ i * xbar i) + (1 / (2 * L)) * ‖sτ - gbar‖ ^ (2 : ℕ) -
        sInf ((fun i => sτ i) '' (Set.univ : Set (Fin n)))
        = (∑ i, sτ i * xbar i) + (1 / (2 * L)) * τ ^ (2 : ℕ) - τ := by
            simp [hnorm, hInf']
    _ = (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (1 / (2 * L)) * τ ^ (2 : ℕ) := by
          linarith [hsum_shift]
    _ = (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (τ ^ (2 : ℕ)) / (2 * L) := by
          ring

/-- Reduce the swapped dual expression to the one-dimensional `τ` infimum. -/
lemma simplexProximalValue_dual_reduce_to_tau_core (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hxbar : xbar ∈ standardSimplex n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) (hL : 0 < L) :
    sInf
        ((fun s : Fin n → ℝ =>
              (∑ i, s i * xbar i) + (1 / (2 * L)) * ‖s - gbar‖ ^ (2 : ℕ) -
                sInf ((fun i => s i) '' (Set.univ : Set (Fin n)))) ''
          (Set.univ : Set (Fin n → ℝ))) =
      sInf
        ((fun τ : ℝ =>
            (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) +
              (τ ^ (2 : ℕ)) / (2 * L)) '' Set.Ici (0 : ℝ)) := by
  classical
  have hn : 0 < n := by
    by_contra hzero
    have hzero' : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst hzero'
    have hsimplex0 : (standardSimplex 0 : Set (Fin 0 → ℝ)) = ∅ := by
      ext x
      simp [standardSimplex]
    have : False := by
      simp [hsimplex0] at hxbar
    exact this
  let Φ : (Fin n → ℝ) → ℝ := fun s =>
    (∑ i, s i * xbar i) + (1 / (2 * L)) * ‖s - gbar‖ ^ (2 : ℕ) -
      sInf ((fun i => s i) '' (Set.univ : Set (Fin n)))
  let Ψ : ℝ → ℝ := fun τ =>
    (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) + (τ ^ (2 : ℕ)) / (2 * L)
  have hne_left : (Φ '' (Set.univ : Set (Fin n → ℝ))).Nonempty := by
    refine ⟨Φ 0, ⟨0, by simp, rfl⟩⟩
  have hne_right : (Ψ '' Set.Ici (0 : ℝ)).Nonempty := by
    refine ⟨Ψ 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hbd_right : BddBelow (Ψ '' Set.Ici (0 : ℝ)) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨τ, hτ, rfl⟩
    have hxbar_nonneg : ∀ i, 0 ≤ xbar i := hxbar.1
    have hsum_nonneg :
        0 ≤ ∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hmax_nonneg : 0 ≤ max (gbar i - (2 : ℝ) * τ) 0 := by
        exact le_max_right _ _
      exact mul_nonneg (hxbar_nonneg i) hmax_nonneg
    have hquad_nonneg : 0 ≤ (τ ^ (2 : ℕ)) / (2 * L) := by
      have hτsq : 0 ≤ τ ^ (2 : ℕ) := by
        simpa using pow_two_nonneg τ
      have hden : 0 ≤ 2 * L := by linarith [hL]
      exact div_nonneg hτsq hden
    linarith
  have hlower : ∀ s : Fin n → ℝ, sInf (Ψ '' Set.Ici (0 : ℝ)) ≤ Φ s := by
    intro s
    let τ : ℝ := ‖s - gbar‖
    have hτ : 0 ≤ τ := by exact norm_nonneg _
    have hbound :
        Φ s ≥ Ψ τ := by
      simpa [Φ, Ψ, τ] using
        (simplexProximalValue_dual_reduce_to_tau_lower_bound (n := n) (xbar := xbar)
          (gbar := gbar) (L := L) hn hxbar hmin s)
    have hmem : Ψ τ ∈ (Ψ '' Set.Ici (0 : ℝ)) := by
      exact ⟨τ, hτ, rfl⟩
    have hle : sInf (Ψ '' Set.Ici (0 : ℝ)) ≤ Ψ τ := csInf_le hbd_right hmem
    linarith
  have hbd_left : BddBelow (Φ '' (Set.univ : Set (Fin n → ℝ))) := by
    refine ⟨sInf (Ψ '' Set.Ici (0 : ℝ)), ?_⟩
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hlower s
  have hle_right : sInf (Ψ '' Set.Ici (0 : ℝ)) ≤ sInf (Φ '' (Set.univ : Set (Fin n → ℝ))) := by
    refine le_csInf hne_left ?_
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hlower s
  have hupper :
      ∀ τ ∈ Set.Ici (0 : ℝ),
        sInf (Φ '' (Set.univ : Set (Fin n → ℝ))) ≤ Ψ τ := by
    intro τ hτ
    rcases
        simplexProximalValue_dual_reduce_to_tau_construct (n := n) (xbar := xbar) (gbar := gbar)
          (L := L) hn hxbar hmin (τ := τ) hτ with ⟨s, hs⟩
    have hs' : Φ s = Ψ τ := by
      simpa [Φ, Ψ] using hs
    have hmem : Φ s ∈ (Φ '' (Set.univ : Set (Fin n → ℝ))) := by
      exact ⟨s, by simp, rfl⟩
    have hle : sInf (Φ '' (Set.univ : Set (Fin n → ℝ))) ≤ Φ s := csInf_le hbd_left hmem
    have hle' : sInf (Φ '' (Set.univ : Set (Fin n → ℝ))) ≤ Ψ τ := by
      exact le_trans hle (le_of_eq hs')
    simpa [Φ, Ψ] using hle'
  have hle_left :
      sInf (Φ '' (Set.univ : Set (Fin n → ℝ))) ≤ sInf (Ψ '' Set.Ici (0 : ℝ)) := by
    refine le_csInf hne_right ?_
    intro y hy
    rcases hy with ⟨τ, hτ, rfl⟩
    exact hupper τ hτ
  exact le_antisymm hle_left hle_right

/-- Reduce the swapped dual expression to the one-dimensional `τ` infimum. -/
lemma simplexProximalValue_dual_reduce_to_tau (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hxbar : xbar ∈ standardSimplex n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) (hL : 0 < L) :
    - sSup
          ((fun s : Fin n → ℝ =>
                (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                  sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
            (Set.univ : Set (Fin n → ℝ))) =
      sInf
        ((fun τ : ℝ =>
            (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) +
              (τ ^ (2 : ℕ)) / (2 * L)) '' Set.Ici (0 : ℝ)) := by
  classical
  let Φ : (Fin n → ℝ) → ℝ := fun s =>
    (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
      sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))
  have hneg :
      - sSup ((fun s => Φ s) '' (Set.univ : Set (Fin n → ℝ))) =
        sInf ((fun s => -Φ s) '' (Set.univ : Set (Fin n → ℝ))) := by
    have h :=
      (Section04Part10.sInf_image_neg_eq_neg_sSup
        (s := (fun s => Φ s) '' (Set.univ : Set (Fin n → ℝ)))).symm
    rw [Set.image_image] at h
    exact h
  have hrewrite :
      sInf ((fun s => -Φ s) '' (Set.univ : Set (Fin n → ℝ))) =
        sInf
          ((fun t : Fin n → ℝ =>
                (∑ i, t i * xbar i) + (1 / (2 * L)) * ‖t - gbar‖ ^ (2 : ℕ) -
                  sInf ((fun i => t i) '' (Set.univ : Set (Fin n)))) ''
            (Set.univ : Set (Fin n → ℝ))) := by
    have himage :
        ((fun s => -Φ s) '' (Set.univ : Set (Fin n → ℝ))) =
          ((fun t : Fin n → ℝ =>
                (∑ i, t i * xbar i) + (1 / (2 * L)) * ‖t - gbar‖ ^ (2 : ℕ) -
                  sInf ((fun i => t i) '' (Set.univ : Set (Fin n)))) ''
            (Set.univ : Set (Fin n → ℝ))) := by
      ext y
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨fun i => gbar i + s i, by simp, ?_⟩
        have hsub : (fun i => gbar i + s i) - gbar = s := by
          funext i
          simp [Pi.sub_apply]
        change
            (∑ i, (gbar i + s i) * xbar i) + (1 / (2 * L)) * ‖(fun i => gbar i + s i) - gbar‖ ^
                  (2 : ℕ) -
                sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n))) =
              -Φ s
        rw [hsub]
        simp [Φ, sub_eq_add_neg]
        ring_nf
      · rintro ⟨t, ht, rfl⟩
        refine ⟨fun i => t i - gbar i, by simp, ?_⟩
        have hsum : (fun i => gbar i + (t i - gbar i)) = t := by
          funext i
          ring_nf
        change
            -Φ (fun i => t i - gbar i) =
              (∑ i, t i * xbar i) + (1 / (2 * L)) * ‖t - gbar‖ ^ (2 : ℕ) -
                sInf ((fun i => t i) '' (Set.univ : Set (Fin n)))
        simp [Φ, sub_eq_add_neg]
        have hnorm : ‖t + -gbar‖ = ‖fun i => t i + -gbar i‖ := rfl
        simp [hnorm]
        ring_nf
    simp [himage]
  have hcore :=
    simplexProximalValue_dual_reduce_to_tau_core (n := n) (xbar := xbar) (gbar := gbar)
      (L := L) (hxbar := hxbar) (hmin := hmin) (hL := hL)
  calc
    - sSup
        ((fun s : Fin n → ℝ =>
              (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
          (Set.univ : Set (Fin n → ℝ))) =
        - sSup ((fun s => Φ s) '' (Set.univ : Set (Fin n → ℝ))) := by
          simp [Φ]
    _ =
        sInf ((fun s => -Φ s) '' (Set.univ : Set (Fin n → ℝ))) := hneg
    _ =
        sInf
          ((fun t : Fin n → ℝ =>
                (∑ i, t i * xbar i) + (1 / (2 * L)) * ‖t - gbar‖ ^ (2 : ℕ) -
                  sInf ((fun i => t i) '' (Set.univ : Set (Fin n)))) ''
            (Set.univ : Set (Fin n → ℝ))) := hrewrite
    _ =
        sInf
          ((fun τ : ℝ =>
              (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) +
                (τ ^ (2 : ℕ)) / (2 * L)) '' Set.Ici (0 : ℝ)) := hcore

/-- Proposition 1.5.2.
Assume the setup of Definition 1.5.1 and the normalization (5.2).
Let `‖·‖` denote the `l_infty` norm on `ℝ^n`, so `‖s‖ = max_i |s^{(i)}|`.
Then the optimal value `psi*` of (5.1) satisfies the dual representation
`-psi* = min_{τ ≥ 0} { ∑_{i=1}^n xbar^(i) (gbar^(i) - 2 τ)_+ + τ^2/(2L) }`
with `(a)_+ = max{a,0}` (equation (5.3)).
Consequently, `psi*` can be computed by a one-dimensional search over `τ ≥ 0` after sorting
the components of `gbar`. -/
theorem simplexProximalValue_dual_representation (n : ℕ) (xbar gbar : Fin n → ℝ) (L : ℝ)
    (hxbar : xbar ∈ standardSimplex n)
    (hmin : sInf ((fun i => gbar i) '' (Set.univ : Set (Fin n))) = 0) (hL : 0 < L) :
    - simplexProximalValue n xbar gbar L =
      sInf
        ((fun τ : ℝ =>
            (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) +
              (τ ^ (2 : ℕ)) / (2 * L)) '' Set.Ici (0 : ℝ)) := by
  classical
  have hdual :=
    simplexProximalValue_dual_after_exchange (n := n) (xbar := xbar) (gbar := gbar) (L := L)
      hxbar hL
  calc
    - simplexProximalValue n xbar gbar L =
        - sSup
            ((fun s : Fin n → ℝ =>
                  (-∑ i, (gbar i + s i) * xbar i) - (1 / (2 * L)) * ‖s‖ ^ (2 : ℕ) +
                    sInf ((fun i => gbar i + s i) '' (Set.univ : Set (Fin n)))) ''
              (Set.univ : Set (Fin n → ℝ))) := by
        simp [hdual]
    _ =
        sInf
          ((fun τ : ℝ =>
              (∑ i, xbar i * max (gbar i - (2 : ℝ) * τ) 0) +
                (τ ^ (2 : ℕ)) / (2 * L)) '' Set.Ici (0 : ℝ)) := by
        have hreduce :=
          simplexProximalValue_dual_reduce_to_tau (n := n) (xbar := xbar) (gbar := gbar)
            (L := L) (hxbar := hxbar) (hmin := hmin) (hL := hL)
        simpa [Set.image_univ] using hreduce

/-- Definition 1.5.2.1.
For `μ > 0` and `u ∈ ℝ^m`, define the log-sum-exp smoothing function
`η(u) = μ * log (∑_{j=1}^m exp (u^{(j)} / μ))` (equation (5.4)). -/
noncomputable def logSumExpSmooth (m : ℕ) (μ : ℝ) (u : Fin m → ℝ) : ℝ :=
  μ * Real.log (∑ j, Real.exp (u j / μ))

/-- Shifting the input of log-sum-exp by a constant adds that constant. -/
lemma logSumExpSmooth_add_const (m : ℕ) (μ : ℝ) (hm : 0 < m) (hμ : 0 < μ)
    (u : Fin m → ℝ) (c : ℝ) :
    logSumExpSmooth m μ (fun j => u j + c) = c + logSumExpSmooth m μ u := by
  classical
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hsum_pos : 0 < ∑ j, Real.exp (u j / μ) := by
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ Real.exp (u i / μ) := by
      intro i hi
      exact (Real.exp_pos _).le
    have hmem : (⟨0, hm⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := by
      simp
    have hle : Real.exp (u ⟨0, hm⟩ / μ) ≤ ∑ j, Real.exp (u j / μ) := by
      have hle' :=
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => Real.exp (u i / μ)) hnonneg hmem)
      simpa using hle'
    have hpos : 0 < Real.exp (u ⟨0, hm⟩ / μ) := Real.exp_pos _
    exact lt_of_lt_of_le hpos hle
  have hsum_ne : (∑ j, Real.exp (u j / μ)) ≠ 0 := ne_of_gt hsum_pos
  have hexp_ne : Real.exp (c / μ) ≠ 0 := Real.exp_ne_zero _
  have hsum : (∑ j, Real.exp ((u j + c) / μ)) =
      (∑ j, Real.exp (u j / μ)) * Real.exp (c / μ) := by
    calc
      (∑ j, Real.exp ((u j + c) / μ)) =
          ∑ j, Real.exp (u j / μ) * Real.exp (c / μ) := by
        simp [add_div, Real.exp_add, mul_comm]
      _ = (∑ j, Real.exp (u j / μ)) * Real.exp (c / μ) := by
        symm
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
            (f := fun j => Real.exp (u j / μ)) (a := Real.exp (c / μ)))
  calc
    logSumExpSmooth m μ (fun j => u j + c) =
        μ * Real.log ((∑ j, Real.exp (u j / μ)) * Real.exp (c / μ)) := by
      simp [logSumExpSmooth, hsum]
    _ = μ * Real.log (Real.exp (c / μ) * ∑ j, Real.exp (u j / μ)) := by
      simp [mul_comm]
    _ = μ * (Real.log (Real.exp (c / μ)) + Real.log (∑ j, Real.exp (u j / μ))) := by
      have hlog :=
        Real.log_mul (x := Real.exp (c / μ)) (y := ∑ j, Real.exp (u j / μ)) hexp_ne hsum_ne
      simpa using congrArg (fun t => μ * t) hlog
    _ = μ * ((c / μ) + Real.log (∑ j, Real.exp (u j / μ))) := by
      simp [Real.log_exp]
    _ = c + logSumExpSmooth m μ u := by
      simp [logSumExpSmooth, mul_add, mul_div_cancel₀, hμne]

/-- The derivative of log-sum-exp is invariant under constant shifts. -/
lemma fderiv_logSumExpSmooth_add_const (m : ℕ) (μ : ℝ) (hm : 0 < m) (hμ : 0 < μ)
    (u : Fin m → ℝ) (c : ℝ) :
    fderiv ℝ (logSumExpSmooth m μ) (u + fun _ => c) = fderiv ℝ (logSumExpSmooth m μ) u := by
  classical
  have hfun : (fun x : Fin m → ℝ => logSumExpSmooth m μ (x + fun _ => c)) =
      fun x => c + logSumExpSmooth m μ x := by
    funext x
    simpa using (logSumExpSmooth_add_const (m := m) (μ := μ) hm hμ x c)
  calc
    fderiv ℝ (logSumExpSmooth m μ) (u + fun _ => c) =
        fderiv ℝ (fun x => logSumExpSmooth m μ (x + fun _ => c)) u := by
      simpa using
        (fderiv_comp_add_right (f := logSumExpSmooth m μ) (x := u) (a := fun _ => c)).symm
    _ = fderiv ℝ (fun x => c + logSumExpSmooth m μ x) u := by
      simp [hfun]
    _ = fderiv ℝ (logSumExpSmooth m μ) u := by
      simp [fderiv_const_add]

/-- Proposition 1.5.2.1.
Let `η` be defined by (5.4). For any `u ∈ ℝ^m`, let `\bar u = max_{1 ≤ j ≤ m} u^{(j)}` and define
`v ∈ ℝ^m` by `v^{(j)} = u^{(j)} - \bar u`. Then `η(u) = \bar u + η(v)` and
`\nabla η(u) = \nabla η(v)` (equation (eq:auto_Proposition_5_5_content_1)). -/
theorem logSumExpSmooth_shift (m : ℕ) (μ : ℝ) (hμ : 0 < μ) (u : Fin m → ℝ) :
    let ubar : ℝ := sSup (Set.range u)
    let v : Fin m → ℝ := fun j => u j - ubar
    logSumExpSmooth m μ u = ubar + logSumExpSmooth m μ v ∧
      fderiv ℝ (logSumExpSmooth m μ) u = fderiv ℝ (logSumExpSmooth m μ) v := by
  classical
  cases m with
  | zero =>
      simp [logSumExpSmooth]
  | succ m' =>
      change
        (logSumExpSmooth (m' + 1) μ u =
            sSup (Set.range u) + logSumExpSmooth (m' + 1) μ (fun j ↦ u j - sSup (Set.range u))) ∧
          fderiv ℝ (logSumExpSmooth (m' + 1) μ) u =
            fderiv ℝ (logSumExpSmooth (m' + 1) μ) (fun j ↦ u j - sSup (Set.range u))
      set ubar : ℝ := sSup (Set.range u)
      set v : Fin (m' + 1) → ℝ := fun j => u j - ubar
      have hv : (fun j => v j + ubar) = u := by
        funext j
        simp [v, ubar]
      have hv' : v + (fun _ => ubar) = u := by
        funext j
        simp [v, ubar]
      have hshift :=
        logSumExpSmooth_add_const (m := m' + 1) (μ := μ) (hm := Nat.succ_pos m') hμ v ubar
      have hderiv :=
        fderiv_logSumExpSmooth_add_const (m := m' + 1) (μ := μ) (hm := Nat.succ_pos m') hμ v ubar
      refine And.intro ?h1 ?h2
      · simpa [hv] using hshift
      · simpa [hv'] using hderiv

/-- Definition 1.5.3.1.
Assume `d : Q → ℝ` is differentiable and `σ`-strongly convex on `Q`. Define the Bregman distance
`ξ(z,x) = d x - d z - ⟪∇ d z, x - z⟫` for `z, x ∈ Q`
(equation (eq:auto_Definition_5_6_content_1)). -/
noncomputable def bregmanDistance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : E → ℝ) (z x : E) : ℝ :=
  d x - d z - DualPairing ((fderiv ℝ d z).toLinearMap) (x - z)

/-- Expand the Bregman distance using the Fréchet derivative. -/
lemma bregmanDistance_eq_sub_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : E → ℝ) (z x : E) :
    bregmanDistance d z x = d x - d z - (fderiv ℝ d z) (x - z) := by
  simp [bregmanDistance, DualPairing]

/-- Secant slope bound along the segment from `z` to `x` under strong convexity. -/
lemma strongConvexOn_secant_slope_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ : ℝ} (hconv : StrongConvexOn Q σ d) {z x : E}
    (hz : z ∈ Q) (hx : x ∈ Q) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t⁻¹ * (d (z + t • (x - z)) - d z) ≤
      (d x - d z) - (1 - t) * ((σ / 2) * ‖x - z‖ ^ (2 : ℕ)) := by
  have ht0 : 0 < t := ht.1
  have ha : 0 ≤ 1 - t := by linarith [ht.2]
  have hb : 0 ≤ t := le_of_lt ht0
  have hab : (1 - t) + t = 1 := by ring
  rcases (by simpa [StrongConvexOn] using hconv) with ⟨_, hineq⟩
  set C : ℝ := (σ / 2) * ‖x - z‖ ^ (2 : ℕ)
  have hline : (1 - t) • z + t • x = z + t • (x - z) := by
    calc
      (1 - t) • z + t • x = (1 : ℝ) • z - t • z + t • x := by
        simp [sub_smul]
      _ = z + t • (x - z) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm]
  have hineq' :
      d (z + t • (x - z)) ≤ (1 - t) * d z + t * d x - (1 - t) * t * C := by
    have := hineq (x := z) hz (y := x) hx (a := 1 - t) (b := t) ha hb hab
    simpa [hline, smul_eq_mul, norm_sub_rev, C, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hineq'' :
      d (z + t • (x - z)) - d z ≤ t * (d x - d z) - (1 - t) * t * C := by
    linarith
  have hineq''' :
      d (z + t • (x - z)) - d z ≤ t * ((d x - d z) - (1 - t) * C) := by
    have hfact :
        t * ((d x - d z) - (1 - t) * C) =
          t * (d x - d z) - (1 - t) * t * C := by
      ring
    simpa [hfact] using hineq''
  have hdiv :
      (d (z + t • (x - z)) - d z) / t ≤ (d x - d z) - (1 - t) * C := by
    exact (div_le_iff₀ ht0).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq''')
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, C] using hdiv

/-- Derivative of `t ↦ d (z + t • (x - z))` at `t = 0`. -/
lemma hasDerivAt_bregman_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : E → ℝ} {z x : E} (hdiffz : DifferentiableAt ℝ d z) :
    HasDerivAt (fun t : ℝ => d (z + t • (x - z))) ((fderiv ℝ d z) (x - z)) 0 := by
  have hInner : HasDerivAt (fun t : ℝ => z + t • (x - z)) (x - z) 0 := by
    simpa using
      (HasDerivAt.const_add z ((hasDerivAt_id (0 : ℝ)).smul_const (x - z)))
  have hF : HasFDerivAt d (fderiv ℝ d z) z := by
    simpa using hdiffz.hasFDerivAt
  have hF' : HasFDerivAt d (fderiv ℝ d z) (z + (0 : ℝ) • (x - z)) := by
    simpa using hF
  simpa [Function.comp] using (HasFDerivAt.comp_hasDerivAt (x := 0) hF' hInner)

/-- Convert a right-hand secant bound into a bound on the derivative. -/
lemma deriv_le_of_secant_bound_nhdsGT {φ g : ℝ → ℝ} {φ' G : ℝ}
    (hderiv : HasDerivAt φ φ' 0)
    (hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, t⁻¹ * (φ t - φ 0) ≤ g t)
    (hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 G)) :
    φ' ≤ G := by
  have hslopes :
      Tendsto (fun t => t⁻¹ * (φ t - φ 0)) (𝓝[>] (0 : ℝ)) (𝓝 φ') := by
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
      (hderiv.tendsto_slope_zero_right (x := 0))
  have hEvent : (fun t => t⁻¹ * (φ t - φ 0)) ≤ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hbound t ht
  exact le_of_tendsto_of_tendsto hslopes hlim hEvent

/-- Definition 1.5.3.1.
In the setting of Definition 1.5.3.1, the Bregman distance satisfies
`ξ(z,x) ≥ (σ/2) ‖x - z‖^2` for all `z, x ∈ Q`. -/
theorem bregmanDistance_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {d : E → ℝ} {σ : ℝ}
    (hdiff : ∀ z ∈ Q, DifferentiableAt ℝ d z) (hconv : StrongConvexOn Q σ d) :
    ∀ z ∈ Q, ∀ x ∈ Q,
      bregmanDistance d z x ≥ (1 / 2 : ℝ) * σ * ‖x - z‖ ^ (2 : ℕ) := by
  intro z hz x hx
  set φ : ℝ → ℝ := fun t => d (z + t • (x - z))
  set C : ℝ := (σ / 2) * ‖x - z‖ ^ (2 : ℕ)
  have hderiv : HasDerivAt φ ((fderiv ℝ d z) (x - z)) 0 := by
    simpa [φ] using hasDerivAt_bregman_line (z := z) (x := x) (hdiffz := hdiff z hz)
  have hbound :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, t⁻¹ * (φ t - φ 0) ≤
        (d x - d z) - (1 - t) * C := by
    intro t ht
    simpa [φ, C] using
      (strongConvexOn_secant_slope_bound (hconv := hconv) hz hx ht)
  have hId : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds (a := (0 : ℝ)) (s := Set.Ioi 0)
        (l := 𝓝 (0 : ℝ)) (tendsto_id))
  have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hId)
  have hmul : Tendsto (fun t : ℝ => (1 - t) * C) (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa using (h1.mul tendsto_const_nhds)
  have hlim :
      Tendsto (fun t => (d x - d z) - (1 - t) * C) (𝓝[>] (0 : ℝ))
        (𝓝 ((d x - d z) - C)) := by
    simpa using (tendsto_const_nhds.sub hmul)
  have hle :
      (fderiv ℝ d z) (x - z) ≤ (d x - d z) - C := by
    exact
      (deriv_le_of_secant_bound_nhdsGT (φ := φ) (g := fun t =>
        (d x - d z) - (1 - t) * C) (φ' := (fderiv ℝ d z) (x - z)) (G := (d x - d z) - C)
        hderiv hbound hlim)
  have hle' : d x - d z - (fderiv ℝ d z) (x - z) ≥ C := by
    linarith
  have hC : C = (1 / 2 : ℝ) * σ * ‖x - z‖ ^ (2 : ℕ) := by
    simp [C, div_eq_mul_inv, mul_comm, mul_left_comm]
  have hfinal :
      bregmanDistance d z x ≥ C := by
    simpa [bregmanDistance_eq_sub_fderiv] using hle'
  simpa [hC] using hfinal

/-- Definition 1.5.3.1.
Define the mapping
`V_Q(z,g) = argmin_{x ∈ Q} { ⟪g, x - z⟫ + ξ(z,x) }`
(equation (eq:auto_Definition_5_6_content_2)). -/
noncomputable def V_Q {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (d : E → ℝ) (z : Q)
    (g : Module.Dual ℝ E) : Q := by
  classical
  let Φ : E → ℝ := fun x => DualPairing g (x - z) + bregmanDistance d z x
  by_cases h : ∃ x : Q, IsMinOn Φ Q x
  · exact Classical.choose h
  · exact z

/-- If the minimization problem has a minimizer, `V_Q` selects one. -/
lemma V_Q_spec_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {d : E → ℝ} (z : Q) (g : Module.Dual ℝ E)
    (hmin :
      ∃ x : Q,
        IsMinOn (fun x : E => DualPairing g (x - z) + bregmanDistance d z x) Q x) :
    IsMinOn (fun x : E => DualPairing g (x - z) + bregmanDistance d z x) Q
      (V_Q Q d z g) := by
  classical
  let Φ : E → ℝ := fun x => DualPairing g (x - z) + bregmanDistance d z x
  have hmin' : ∃ x : Q, IsMinOn Φ Q x := by
    simpa [Φ] using hmin
  by_cases h : ∃ x : Q, IsMinOn Φ Q x
  · have hspec : IsMinOn Φ Q ((Classical.choose h : Q) : E) := by
      simpa using (Classical.choose_spec h)
    simpa [V_Q, Φ, h] using hspec
  · exact False.elim (h hmin')

/-- Expand a linear functional on `Fin n → ℝ` in the standard basis. -/
lemma DualPairing_eq_sum_gcoord_standardBasis (n : ℕ)
    (g : Module.Dual ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    DualPairing g x =
      ∑ i : Fin n, (g (fun j : Fin n => if j = i then (1 : ℝ) else 0)) * x i := by
  classical
  have hx :
      x = ∑ i : Fin n, x i • (fun j : Fin n => if j = i then (1 : ℝ) else 0) := by
    simpa [eq_comm] using (pi_eq_sum_univ (x := x) (R := ℝ))
  rw [DualPairing, hx]
  simp [map_sum, smul_eq_mul, mul_comm]

/-- Fréchet derivative of the entropy sum `∑ i, x i * log(x i)` at a positive point. -/
lemma fderiv_entropy_sum (n : ℕ) (z : Fin n → ℝ) (hz_pos : ∀ i, 0 < z i) :
    fderiv ℝ (fun x : Fin n → ℝ => ∑ i, x i * Real.log (x i)) z =
      ∑ i : Fin n,
        (Real.log (z i) + 1) •
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i) := by
  classical
  have hcoord :
      ∀ i : Fin n,
        HasFDerivAt (fun x : Fin n → ℝ => x i * Real.log (x i))
          ((Real.log (z i) + 1) •
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i)) z := by
    intro i
    have heval :
        HasFDerivAt (fun x : Fin n → ℝ => x i)
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i) z := by
      simpa using
        (ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i))
    have hscalar :
        HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log (z i) + 1) (z i) := by
      exact Real.hasDerivAt_mul_log (ne_of_gt (hz_pos i))
    simpa [Function.comp] using
      (HasDerivAt.comp_hasFDerivAt (x := z) hscalar heval)
  have hsum :
      HasFDerivAt (fun x : Fin n → ℝ => ∑ i : Fin n, x i * Real.log (x i))
        (∑ i : Fin n,
          (Real.log (z i) + 1) •
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i)) z := by
    have hsum' :=
      (HasFDerivAt.sum (x := z) (u := Finset.univ)
        (A := fun i : Fin n => fun x : Fin n → ℝ => x i * Real.log (x i))
        (A' := fun i : Fin n =>
          (Real.log (z i) + 1) •
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i))
        (by
          intro i hi
          simpa using hcoord i))
    -- rewrite the sum of functions into a pointwise sum
    convert hsum' using 1
    · funext x
      simp [Finset.sum_apply]
  exact hsum.fderiv

/-- On the simplex, the entropy Bregman distance equals the KL divergence. -/
lemma bregmanDistance_entropy_eq_sum_mul_log_div_on_simplex (n : ℕ) (z : standardSimplex n)
    (x : Fin n → ℝ) (hx : x ∈ standardSimplex n) (hz_pos : ∀ i, 0 < z.1 i) :
    let d : (Fin n → ℝ) → ℝ :=
      fun y => Real.log (n : ℝ) + ∑ i, y i * Real.log (y i)
    bregmanDistance d z x = ∑ i, x i * Real.log (x i / z.1 i) := by
  classical
  intro d
  have hsum : ∑ i, x i = (1 : ℝ) := hx.2
  have hzsum : ∑ i, z.1 i = (1 : ℝ) := z.property.2
  have hderiv_sum :
      fderiv ℝ (fun y : Fin n → ℝ => ∑ i, y i * Real.log (y i)) z.1 =
        ∑ i : Fin n,
          (Real.log (z.1 i) + 1) •
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i) := by
    simpa using fderiv_entropy_sum (n := n) (z := z.1) hz_pos
  have hderiv :
      fderiv ℝ d z.1 =
        ∑ i : Fin n,
          (Real.log (z.1 i) + 1) •
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i) := by
    have hconst :
        fderiv ℝ (fun y : Fin n → ℝ => Real.log (n : ℝ) + ∑ i, y i * Real.log (y i)) z.1 =
          fderiv ℝ (fun y : Fin n → ℝ => ∑ i, y i * Real.log (y i)) z.1 := by
      simp
    calc
      fderiv ℝ d z.1 =
          fderiv ℝ (fun y : Fin n → ℝ => ∑ i, y i * Real.log (y i)) z.1 := by
            simp [d]
      _ =
          ∑ i : Fin n, (Real.log (z.1 i) + 1) • (ContinuousLinearMap.proj i) := hderiv_sum
  have hpair :
      DualPairing ((fderiv ℝ d z.1).toLinearMap) (x - z.1) =
        ∑ i : Fin n, (Real.log (z.1 i) + 1) * (x i - z.1 i) := by
    change (fderiv ℝ d z.1) (x - z.1) =
      ∑ i : Fin n, (Real.log (z.1 i) + 1) * (x i - z.1 i)
    simp [hderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hsum_log :
      ∑ i : Fin n, x i * Real.log (x i / z.1 i) =
        (∑ i : Fin n, x i * Real.log (x i)) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
    have hz_ne : ∀ i, z.1 i ≠ 0 := fun i => ne_of_gt (hz_pos i)
    calc
      ∑ i : Fin n, x i * Real.log (x i / z.1 i) =
          ∑ i : Fin n, (x i * Real.log (x i) - x i * Real.log (z.1 i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (entropySimplex_mul_log_div_eq (u := z.1 i) (v := x i) (hz_ne i))
      _ =
          (∑ i : Fin n, x i * Real.log (x i)) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
            simp [Finset.sum_sub_distrib]
  have hlinx :
      ∑ i : Fin n, (Real.log (z.1 i) + 1) * x i =
        (∑ i : Fin n, x i * Real.log (z.1 i)) + ∑ i : Fin n, x i := by
    calc
      ∑ i : Fin n, (Real.log (z.1 i) + 1) * x i =
          ∑ i : Fin n, (Real.log (z.1 i) * x i + x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ =
          (∑ i : Fin n, Real.log (z.1 i) * x i) + ∑ i : Fin n, x i := by
            simp [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin n, x i * Real.log (z.1 i)) + ∑ i : Fin n, x i := by
            simp [mul_comm]
  have hlinz :
      ∑ i : Fin n, (Real.log (z.1 i) + 1) * z.1 i =
        (∑ i : Fin n, z.1 i * Real.log (z.1 i)) + ∑ i : Fin n, z.1 i := by
    calc
      ∑ i : Fin n, (Real.log (z.1 i) + 1) * z.1 i =
          ∑ i : Fin n, (Real.log (z.1 i) * z.1 i + z.1 i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ =
          (∑ i : Fin n, Real.log (z.1 i) * z.1 i) + ∑ i : Fin n, z.1 i := by
            simp [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin n, z.1 i * Real.log (z.1 i)) + ∑ i : Fin n, z.1 i := by
            simp [mul_comm]
  calc
    bregmanDistance d z x =
        d x - d z.1 - DualPairing ((fderiv ℝ d z.1).toLinearMap) (x - z.1) := by
          rfl
    _ =
        d x - d z.1 - ∑ i : Fin n, (Real.log (z.1 i) + 1) * (x i - z.1 i) := by
          rw [hpair]
    _ =
        (Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)) -
            (Real.log (n : ℝ) + ∑ i, z.1 i * Real.log (z.1 i)) -
          ∑ i : Fin n, (Real.log (z.1 i) + 1) * (x i - z.1 i) := by
          simp [d]
    _ =
        (∑ i, x i * Real.log (x i)) - (∑ i, z.1 i * Real.log (z.1 i)) -
          ∑ i : Fin n, (Real.log (z.1 i) + 1) * (x i - z.1 i) := by
          ring
    _ =
        (∑ i, x i * Real.log (x i)) - (∑ i, z.1 i * Real.log (z.1 i)) -
          ((∑ i, (Real.log (z.1 i) + 1) * x i) -
            ∑ i, (Real.log (z.1 i) + 1) * z.1 i) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ =
        (∑ i, x i * Real.log (x i)) - (∑ i, z.1 i * Real.log (z.1 i)) -
            (∑ i, (Real.log (z.1 i) + 1) * x i) +
          ∑ i, (Real.log (z.1 i) + 1) * z.1 i := by
          ring
    _ =
        (∑ i, x i * Real.log (x i)) - (∑ i, z.1 i * Real.log (z.1 i)) -
            ((∑ i, x i * Real.log (z.1 i)) + ∑ i, x i) +
          ((∑ i, z.1 i * Real.log (z.1 i)) + ∑ i, z.1 i) := by
          simp [hlinx, hlinz]
    _ =
        (∑ i, x i * Real.log (x i)) - ∑ i, x i * Real.log (z.1 i) -
          (∑ i, x i) + ∑ i, z.1 i := by
          ring
    _ = (∑ i, x i * Real.log (x i)) - ∑ i, x i * Real.log (z.1 i) := by
          simp [hsum, hzsum]
    _ = ∑ i, x i * Real.log (x i / z.1 i) := by
          simpa using hsum_log.symm
