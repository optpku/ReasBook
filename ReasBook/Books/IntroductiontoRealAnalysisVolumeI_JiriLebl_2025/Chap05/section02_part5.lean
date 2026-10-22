/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section02_part4

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02
lemma bounded_of_eq_off_finite {a b : ℝ} {f g : ℝ → ℝ} {S : Set ℝ}
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hfin : S.Finite)
    (hfg : ∀ x ∈ Set.Icc a b \ S, g x = f x) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M := by
  classical
  rcases hbound with ⟨M, hM⟩
  let T : Finset ℝ := hfin.toFinset.filter (fun x => x ∈ Set.Icc a b)
  by_cases hT : T.Nonempty
  · have hTimage :
        (T.image (fun x => |g x|)).Nonempty := by
      rcases hT with ⟨x, hx⟩
      refine ⟨|g x|, ?_⟩
      exact Finset.mem_image.2 ⟨x, hx, rfl⟩
    let M' : ℝ := max M (Finset.max' (T.image (fun x => |g x|)) hTimage)
    refine ⟨M', ?_⟩
    intro x hx
    by_cases hxS : x ∈ S
    · have hxmem : x ∈ hfin.toFinset := (hfin.mem_toFinset).2 hxS
      have hxT : x ∈ T := (Finset.mem_filter).2 ⟨hxmem, hx⟩
      have hximage : |g x| ∈ T.image (fun x => |g x|) := by
        exact Finset.mem_image.2 ⟨x, hxT, rfl⟩
      have hle_max :
          |g x| ≤ Finset.max' (T.image (fun x => |g x|)) hTimage := by
        simpa using
          (Finset.le_max' (s := T.image (fun x => |g x|)) (x := |g x|) hximage)
      exact le_trans hle_max (le_max_right _ _)
    · have hxfg : g x = f x := hfg x ⟨hx, hxS⟩
      have hbound_x : |g x| ≤ M := by
        simpa [hxfg] using hM x hx
      exact le_trans hbound_x (le_max_left _ _)
  · refine ⟨M, ?_⟩
    intro x hx
    have hxS : x ∉ S := by
      intro hxS
      have hxmem : x ∈ hfin.toFinset := (hfin.mem_toFinset).2 hxS
      have hxT : x ∈ T := (Finset.mem_filter).2 ⟨hxmem, hx⟩
      exact hT ⟨x, hxT⟩
    have hxfg : g x = f x := hfg x ⟨hx, hxS⟩
    simpa [hxfg] using hM x hx

lemma riemannIntegral_eq_zero_of_eq_zero_on_Icc {a b : ℝ} {h : ℝ → ℝ}
    (hab : a ≤ b) (hzero : ∀ x ∈ Set.Icc a b, h x = 0) :
    ∃ hh : RiemannIntegrableOn h a b, riemannIntegral h a b hh = 0 := by
  classical
  obtain ⟨h0, h0eq⟩ := constant_function_riemannIntegral 0 a b hab
  obtain ⟨hh, hEq⟩ :=
    riemannIntegral_congr_on_Icc (a := a) (b := b) (f := fun _ : ℝ => 0) (g := h) hzero h0
  refine ⟨hh, ?_⟩
  simpa [h0eq] using hEq

/-- Each subinterval of a partition lies in the ambient interval. -/
lemma intervalPartition_subinterval_subset {a b : ℝ} (P : IntervalPartition a b) (i : Fin P.n) :
    Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) ⊆ Set.Icc a b := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have hmono : Monotone P.points := P.mono.monotone
  have hleft : a ≤ P.points (Fin.castSucc i) := by
    have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
    simpa [P.left_eq] using h0
  have hright : P.points i.succ ≤ b := by
    have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
    simpa [P.right_eq, Fin.last] using hlast
  exact ⟨le_trans hleft hx1, le_trans hx2 hright⟩

/-- Upper tag bound on a bounded interval. -/
lemma upperTag_le_of_bound {a b : ℝ} {h : ℝ → ℝ} {M : ℝ}
    (P : IntervalPartition a b) (i : Fin P.n)
    (hmax : ∀ x ∈ Set.Icc a b, h x ≤ M) :
    upperTag h P i ≤ M := by
  refine csSup_le ?_ ?_
  · refine ⟨h (P.points (Fin.castSucc i)), ?_⟩
    refine ⟨P.points (Fin.castSucc i), ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxIcc : x ∈ Set.Icc a b := intervalPartition_subinterval_subset P i hx
    exact hmax x hxIcc

/-- Lower tag bound on a bounded interval. -/
lemma lowerTag_ge_of_bound {a b : ℝ} {h : ℝ → ℝ} {M : ℝ}
    (P : IntervalPartition a b) (i : Fin P.n)
    (hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x) :
    -M ≤ lowerTag h P i := by
  refine le_csInf ?_ ?_
  · refine ⟨h (P.points (Fin.castSucc i)), ?_⟩
    refine ⟨P.points (Fin.castSucc i), ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxIcc : x ∈ Set.Icc a b := intervalPartition_subinterval_subset P i hx
    exact hmin x hxIcc

/-- Tag gap bound when `h` is bounded by `±M` on `[a, b]`. -/
lemma tag_gap_le_two_M {a b : ℝ} {h : ℝ → ℝ} {M : ℝ} {P : IntervalPartition a b}
    (hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x)
    (hmax : ∀ x ∈ Set.Icc a b, h x ≤ M) (i : Fin P.n) :
    upperTag h P i - lowerTag h P i ≤ 2 * M := by
  have hupper : upperTag h P i ≤ M := upperTag_le_of_bound (P := P) (i := i) hmax
  have hlower : -M ≤ lowerTag h P i := lowerTag_ge_of_bound (P := P) (i := i) hmin
  linarith

/-- Sum over `Fin n` when `n = 2`. -/
lemma sum_fin_two_eq {n : ℕ} (h : n = 2) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) = f ⟨0, by simp [h]⟩ + f ⟨1, by simp [h]⟩ := by
  cases h
  simp [Fin.sum_univ_two]

/-- Two-step gap bound when the right subinterval contributes zero. -/
lemma upper_lower_gap_two_steps_right_zero {a b : ℝ} {h : ℝ → ℝ} {M δ : ℝ}
    (P : IntervalPartition a b) (hP : P.n = 2)
    (hzero :
      upperTag h P ⟨1, by simp [hP]⟩ = 0 ∧
        lowerTag h P ⟨1, by simp [hP]⟩ = 0)
    (htag0 :
      upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩ ≤ 2 * M)
    (hdelta0 : P.delta ⟨0, by simp [hP]⟩ = δ) :
    upperDarbouxSum h P - lowerDarbouxSum h P ≤ 2 * M * δ := by
  classical
  have hsum :
      upperDarbouxSum h P - lowerDarbouxSum h P =
        (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
        P.delta ⟨0, by simp [hP]⟩ +
          (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
        P.delta ⟨1, by simp [hP]⟩ := by
    have hsum_upper :
        upperDarbouxSum h P =
          upperTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
            upperTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩ := by
      simpa [upperDarbouxSum] using
        (sum_fin_two_eq (n := P.n) (h := hP)
          (f := fun i => upperTag h P i * P.delta i))
    have hsum_lower :
        lowerDarbouxSum h P =
          lowerTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
            lowerTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩ := by
      simpa [lowerDarbouxSum] using
        (sum_fin_two_eq (n := P.n) (h := hP)
          (f := fun i => lowerTag h P i * P.delta i))
    calc
      upperDarbouxSum h P - lowerDarbouxSum h P
          = (upperTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
              upperTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩) -
            (lowerTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
              lowerTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩) := by
                simp [hsum_upper, hsum_lower]
      _ = (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
      P.delta ⟨0, by simp [hP]⟩ +
          (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
          P.delta ⟨1, by simp [hP]⟩ := by
            ring
  have hterm1 : (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
      P.delta ⟨1, by simp [hP]⟩ = 0 := by
    rcases hzero with ⟨hup, hlow⟩
    simp [hup, hlow]
  have hdelta_nonneg : 0 ≤ P.delta ⟨0, by simp [hP]⟩ := by
    exact le_of_lt (sub_pos.mpr (P.mono (Fin.castSucc_lt_succ (i := ⟨0, by simp [hP]⟩))))
  have hmul :
      (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) * P.delta ⟨0, by simp [hP]⟩
        ≤ (2 * M) * P.delta ⟨0, by simp [hP]⟩ :=
    mul_le_mul_of_nonneg_right htag0 hdelta_nonneg
  calc
    upperDarbouxSum h P - lowerDarbouxSum h P
        = (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
          P.delta ⟨0, by simp [hP]⟩ := by
          simpa [hterm1] using hsum
    _ ≤ (2 * M) * δ := by
          simpa [hdelta0, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Two-step gap bound when the left subinterval contributes zero. -/
lemma upper_lower_gap_two_steps_left_zero {a b : ℝ} {h : ℝ → ℝ} {M δ : ℝ}
    (P : IntervalPartition a b) (hP : P.n = 2)
    (hzero :
      upperTag h P ⟨0, by simp [hP]⟩ = 0 ∧
        lowerTag h P ⟨0, by simp [hP]⟩ = 0)
    (htag1 :
      upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩ ≤ 2 * M)
    (hdelta1 : P.delta ⟨1, by simp [hP]⟩ = δ) :
    upperDarbouxSum h P - lowerDarbouxSum h P ≤ 2 * M * δ := by
  classical
  have hsum :
      upperDarbouxSum h P - lowerDarbouxSum h P =
        (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
        P.delta ⟨0, by simp [hP]⟩ +
          (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
          P.delta ⟨1, by simp [hP]⟩ := by
    have hsum_upper :
        upperDarbouxSum h P =
          upperTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
            upperTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩ := by
      simpa [upperDarbouxSum] using
        (sum_fin_two_eq (n := P.n) (h := hP)
          (f := fun i => upperTag h P i * P.delta i))
    have hsum_lower :
        lowerDarbouxSum h P =
          lowerTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
            lowerTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩ := by
      simpa [lowerDarbouxSum] using
        (sum_fin_two_eq (n := P.n) (h := hP)
          (f := fun i => lowerTag h P i * P.delta i))
    calc
      upperDarbouxSum h P - lowerDarbouxSum h P
          = (upperTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
              upperTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩) -
            (lowerTag h P ⟨0, by simp [hP]⟩ * P.delta ⟨0, by simp [hP]⟩ +
              lowerTag h P ⟨1, by simp [hP]⟩ * P.delta ⟨1, by simp [hP]⟩) := by
                simp [hsum_upper, hsum_lower]
      _ = (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
        P.delta ⟨0, by simp [hP]⟩ +
          (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
          P.delta ⟨1, by simp [hP]⟩ := by
            ring
  have hterm0 : (upperTag h P ⟨0, by simp [hP]⟩ - lowerTag h P ⟨0, by simp [hP]⟩) *
      P.delta ⟨0, by simp [hP]⟩ = 0 := by
    rcases hzero with ⟨hup, hlow⟩
    simp [hup, hlow]
  have hdelta_nonneg : 0 ≤ P.delta ⟨1, by simp [hP]⟩ := by
    exact le_of_lt (sub_pos.mpr (P.mono (Fin.castSucc_lt_succ (i := ⟨1, by simp [hP]⟩))))
  have hmul :
      (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) * P.delta ⟨1, by simp [hP]⟩
        ≤ (2 * M) * P.delta ⟨1, by simp [hP]⟩ :=
    mul_le_mul_of_nonneg_right htag1 hdelta_nonneg
  calc
    upperDarbouxSum h P - lowerDarbouxSum h P
        = (upperTag h P ⟨1, by simp [hP]⟩ - lowerTag h P ⟨1, by simp [hP]⟩) *
        P.delta ⟨1, by simp [hP]⟩ := by
          simpa [hterm0] using hsum
    _ ≤ (2 * M) * δ := by
          simpa [hdelta1, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Convert a `2 * M * δ` gap bound into an `ε`-bound. -/
lemma gap_lt_of_le_twoM_delta {α M δ ε : ℝ}
    (hMpos : 0 < M) (hδ_le : δ ≤ ε / (4 * M))
    (hgap : α ≤ 2 * M * δ) (hε : 0 < ε) : α < ε := by
  have hδ' : 2 * M * δ ≤ ε / 2 := by
    have h' : 2 * M * δ ≤ 2 * M * (ε / (4 * M)) :=
      mul_le_mul_of_nonneg_left hδ_le (by nlinarith [hMpos])
    have hne : M ≠ 0 := by nlinarith
    have hcalc : 2 * M * (ε / (4 * M)) = ε / 2 := by
        field_simp [hne]
        ring
    exact by simpa [hcalc] using h'
  have hε' : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt (le_trans hgap hδ') hε'

/-- Convert a `4 * M * δ` gap bound into an `ε`-bound. -/
lemma gap_lt_of_le_fourM_delta {α M δ ε : ℝ}
    (hMpos : 0 < M) (hδ_le : δ ≤ ε / (8 * M))
    (hgap : α ≤ 4 * M * δ) (hε : 0 < ε) : α < ε := by
  have hδ' : 4 * M * δ ≤ ε / 2 := by
    have h' : 4 * M * δ ≤ 4 * M * (ε / (8 * M)) :=
      mul_le_mul_of_nonneg_left hδ_le (by nlinarith [hMpos])
    have hne : M ≠ 0 := by nlinarith
    have hcalc : 4 * M * (ε / (8 * M)) = ε / 2 := by
        field_simp [hne]
        ring
    exact by simpa [hcalc] using h'
  have hε' : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt (le_trans hgap hδ') hε'



end Section02
end Chap05
