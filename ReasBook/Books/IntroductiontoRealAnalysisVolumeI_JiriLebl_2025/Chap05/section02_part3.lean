/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section02_part2

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02
set_option maxHeartbeats 800000 in
-- Needed for the long Darboux-sum argument to elaborate without timeouts.
/-- Proposition 5.2.4 (Linearity): Let `f` and `g` be Riemann integrable on the
closed interval `[a, b]` and let `α : ℝ`.
* (i) The scalar multiple `α • f` belongs to `ℛ([a, b])` and
  `∫_a^b α • f = α * ∫_a^b f`.
* (ii) The sum `f + g` belongs to `ℛ([a, b])` and
  `∫_a^b (f + g) = ∫_a^b f + ∫_a^b g`. -/
lemma riemannIntegral_linearity {a b α : ℝ} {f g : ℝ → ℝ}
    (hf : RiemannIntegrableOn f a b) (hg : RiemannIntegrableOn g a b) :
    (∃ hαf : RiemannIntegrableOn (fun x => α * f x) a b,
        riemannIntegral (fun x => α * f x) a b hαf =
          α * riemannIntegral f a b hf) ∧
      ∃ hfg : RiemannIntegrableOn (fun x => f x + g x) a b,
        riemannIntegral (fun x => f x + g x) a b hfg =
          riemannIntegral f a b hf + riemannIntegral g a b hg := by
  classical
  constructor
  · rcases hf with ⟨hbound_f, hEq_f⟩
    have hbound_αf : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |α * f x| ≤ M := by
      rcases hbound_f with ⟨M, hM⟩
      refine ⟨|α| * M, ?_⟩
      intro x hx
      have hM' := hM x hx
      calc
        |α * f x| = |α| * |f x| := by
          simp
        _ ≤ |α| * M := by
          exact mul_le_mul_of_nonneg_left hM' (abs_nonneg α)
    by_cases hα : 0 ≤ α
    · have lowerTag_mul_nonneg :
          ∀ (P : IntervalPartition a b) (i : Fin P.n),
            lowerTag (fun x => α * f x) P i = α * lowerTag f P i := by
        intro P i
        have himage :
            (fun x => α * f x) '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
              α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            refine ⟨f x, ?_, by simp [smul_eq_mul]⟩
            exact ⟨x, hx, rfl⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        calc
          lowerTag (fun x => α * f x) P i =
              sInf (α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))) := by
                simp [lowerTag, himage]
          _ = α • sInf (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
                simpa using Real.sInf_smul_of_nonneg (a := α) hα
                  (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))
          _ = α * lowerTag f P i := by
                rfl
      have upperTag_mul_nonneg :
          ∀ (P : IntervalPartition a b) (i : Fin P.n),
            upperTag (fun x => α * f x) P i = α * upperTag f P i := by
        intro P i
        have himage :
            (fun x => α * f x) '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
              α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            refine ⟨f x, ?_, by simp [smul_eq_mul]⟩
            exact ⟨x, hx, rfl⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        calc
          upperTag (fun x => α * f x) P i =
              sSup (α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))) := by
                simp [upperTag, himage]
          _ = α • sSup (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
                simpa using Real.sSup_smul_of_nonneg (a := α) hα
                  (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))
          _ = α * upperTag f P i := by
                rfl
      have lowerSum_mul_nonneg (P : IntervalPartition a b) :
          lowerDarbouxSum (fun x => α * f x) P = α * lowerDarbouxSum f P := by
        classical
        calc
          lowerDarbouxSum (fun x => α * f x) P =
              ∑ i : Fin P.n, lowerTag (fun x => α * f x) P i * P.delta i := by
                rfl
          _ = ∑ i : Fin P.n, (α * lowerTag f P i) * P.delta i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [lowerTag_mul_nonneg]
          _ = ∑ i : Fin P.n, α * (lowerTag f P i * P.delta i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_assoc]
          _ = α * ∑ i : Fin P.n, lowerTag f P i * P.delta i := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n)))
                    (f := fun i => lowerTag f P i * P.delta i) α).symm
          _ = α * lowerDarbouxSum f P := by
                rfl
      have upperSum_mul_nonneg (P : IntervalPartition a b) :
          upperDarbouxSum (fun x => α * f x) P = α * upperDarbouxSum f P := by
        classical
        calc
          upperDarbouxSum (fun x => α * f x) P =
              ∑ i : Fin P.n, upperTag (fun x => α * f x) P i * P.delta i := by
                rfl
          _ = ∑ i : Fin P.n, (α * upperTag f P i) * P.delta i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [upperTag_mul_nonneg]
          _ = ∑ i : Fin P.n, α * (upperTag f P i * P.delta i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_assoc]
          _ = α * ∑ i : Fin P.n, upperTag f P i * P.delta i := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n)))
                    (f := fun i => upperTag f P i * P.delta i) α).symm
          _ = α * upperDarbouxSum f P := by
                rfl
      have hLowerInt :
          lowerDarbouxIntegral (fun x => α * f x) a b =
            α * lowerDarbouxIntegral f a b := by
        classical
        calc
          lowerDarbouxIntegral (fun x => α * f x) a b =
              iSup (fun P : IntervalPartition a b =>
                lowerDarbouxSum (fun x => α * f x) P) := by
                simp [lowerDarbouxIntegral, sSup_range]
          _ = iSup (fun P : IntervalPartition a b => α * lowerDarbouxSum f P) := by
                refine iSup_congr ?_
                intro P
                simp [lowerSum_mul_nonneg]
          _ = α * iSup (fun P : IntervalPartition a b => lowerDarbouxSum f P) := by
                simpa [smul_eq_mul] using
                  (Real.smul_iSup_of_nonneg (a := α) hα
                    (f := fun P : IntervalPartition a b => lowerDarbouxSum f P)).symm
          _ = α * lowerDarbouxIntegral f a b := by
                simp [lowerDarbouxIntegral, sSup_range]
      have hUpperInt :
          upperDarbouxIntegral (fun x => α * f x) a b =
            α * upperDarbouxIntegral f a b := by
        classical
        calc
          upperDarbouxIntegral (fun x => α * f x) a b =
              iInf (fun P : IntervalPartition a b =>
                upperDarbouxSum (fun x => α * f x) P) := by
                simp [upperDarbouxIntegral, sInf_range]
          _ = iInf (fun P : IntervalPartition a b => α * upperDarbouxSum f P) := by
                refine iInf_congr ?_
                intro P
                simp [upperSum_mul_nonneg]
          _ = α * iInf (fun P : IntervalPartition a b => upperDarbouxSum f P) := by
                simpa [smul_eq_mul] using
                  (Real.smul_iInf_of_nonneg (a := α) hα
                    (f := fun P : IntervalPartition a b => upperDarbouxSum f P)).symm
          _ = α * upperDarbouxIntegral f a b := by
                simp [upperDarbouxIntegral, sInf_range]
      have hEq_αf :
          lowerDarbouxIntegral (fun x => α * f x) a b =
            upperDarbouxIntegral (fun x => α * f x) a b := by
        calc
          lowerDarbouxIntegral (fun x => α * f x) a b =
              α * lowerDarbouxIntegral f a b := hLowerInt
          _ = α * upperDarbouxIntegral f a b := by
              simp [hEq_f]
          _ = upperDarbouxIntegral (fun x => α * f x) a b := by
              simp [hUpperInt]
      have hαf : RiemannIntegrableOn (fun x => α * f x) a b := ⟨hbound_αf, hEq_αf⟩
      refine ⟨hαf, ?_⟩
      simp [riemannIntegral, hLowerInt]
    · have hα' : α ≤ 0 := le_of_not_ge hα
      have lowerTag_mul_nonpos :
          ∀ (P : IntervalPartition a b) (i : Fin P.n),
            lowerTag (fun x => α * f x) P i = α * upperTag f P i := by
        intro P i
        have himage :
            (fun x => α * f x) '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
              α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            refine ⟨f x, ?_, by simp [smul_eq_mul]⟩
            exact ⟨x, hx, rfl⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        calc
          lowerTag (fun x => α * f x) P i =
              sInf (α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))) := by
                simp [lowerTag, himage]
          _ = α • sSup (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
                simpa using Real.sInf_smul_of_nonpos (a := α) hα'
                  (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))
          _ = α * upperTag f P i := by
                rfl
      have upperTag_mul_nonpos :
          ∀ (P : IntervalPartition a b) (i : Fin P.n),
            upperTag (fun x => α * f x) P i = α * lowerTag f P i := by
        intro P i
        have himage :
            (fun x => α * f x) '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
              α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            refine ⟨f x, ?_, by simp [smul_eq_mul]⟩
            exact ⟨x, hx, rfl⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        calc
          upperTag (fun x => α * f x) P i =
              sSup (α • (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))) := by
                simp [upperTag, himage]
          _ = α • sInf (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
                exact Real.sSup_smul_of_nonpos (a := α) hα'
                  (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))
          _ = α * lowerTag f P i := by
                rfl
      have lowerSum_mul_nonpos (P : IntervalPartition a b) :
          lowerDarbouxSum (fun x => α * f x) P = α * upperDarbouxSum f P := by
        classical
        calc
          lowerDarbouxSum (fun x => α * f x) P =
              ∑ i : Fin P.n, lowerTag (fun x => α * f x) P i * P.delta i := by
                rfl
          _ = ∑ i : Fin P.n, (α * upperTag f P i) * P.delta i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [lowerTag_mul_nonpos]
          _ = ∑ i : Fin P.n, α * (upperTag f P i * P.delta i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_assoc]
          _ = α * ∑ i : Fin P.n, upperTag f P i * P.delta i := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n)))
                    (f := fun i => upperTag f P i * P.delta i) α).symm
          _ = α * upperDarbouxSum f P := by
                rfl
      have upperSum_mul_nonpos (P : IntervalPartition a b) :
          upperDarbouxSum (fun x => α * f x) P = α * lowerDarbouxSum f P := by
        classical
        calc
          upperDarbouxSum (fun x => α * f x) P =
              ∑ i : Fin P.n, upperTag (fun x => α * f x) P i * P.delta i := by
                rfl
          _ = ∑ i : Fin P.n, (α * lowerTag f P i) * P.delta i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [upperTag_mul_nonpos]
          _ = ∑ i : Fin P.n, α * (lowerTag f P i * P.delta i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_assoc]
          _ = α * ∑ i : Fin P.n, lowerTag f P i * P.delta i := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n)))
                    (f := fun i => lowerTag f P i * P.delta i) α).symm
          _ = α * lowerDarbouxSum f P := by
                rfl
      have hLowerInt :
          lowerDarbouxIntegral (fun x => α * f x) a b =
            α * upperDarbouxIntegral f a b := by
        classical
        calc
          lowerDarbouxIntegral (fun x => α * f x) a b =
              iSup (fun P : IntervalPartition a b =>
                lowerDarbouxSum (fun x => α * f x) P) := by
                simp [lowerDarbouxIntegral, sSup_range]
          _ = iSup (fun P : IntervalPartition a b => α * upperDarbouxSum f P) := by
                refine iSup_congr ?_
                intro P
                simp [lowerSum_mul_nonpos]
          _ = α * iInf (fun P : IntervalPartition a b => upperDarbouxSum f P) := by
                simpa [smul_eq_mul] using
                  (Real.smul_iInf_of_nonpos (a := α) hα'
                    (f := fun P : IntervalPartition a b => upperDarbouxSum f P)).symm
          _ = α * upperDarbouxIntegral f a b := by
                change
                  α * iInf (fun P : IntervalPartition a b => upperDarbouxSum f P) =
                    α * sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P))
                exact (congrArg (fun x => α * x)
                  (sInf_range (f := fun P : IntervalPartition a b => upperDarbouxSum f P))).symm
      have hUpperInt :
          upperDarbouxIntegral (fun x => α * f x) a b =
            α * lowerDarbouxIntegral f a b := by
        classical
        calc
          upperDarbouxIntegral (fun x => α * f x) a b =
              iInf (fun P : IntervalPartition a b =>
                upperDarbouxSum (fun x => α * f x) P) := by
                change
                  sInf (Set.range (fun P : IntervalPartition a b =>
                    upperDarbouxSum (fun x => α * f x) P)) =
                    iInf (fun P : IntervalPartition a b =>
                      upperDarbouxSum (fun x => α * f x) P)
                exact (sInf_range (f := fun P : IntervalPartition a b =>
                  upperDarbouxSum (fun x => α * f x) P))
          _ = iInf (fun P : IntervalPartition a b => α * lowerDarbouxSum f P) := by
                refine iInf_congr ?_
                intro P
                simp [upperSum_mul_nonpos]
          _ = α * iSup (fun P : IntervalPartition a b => lowerDarbouxSum f P) := by
                simpa [smul_eq_mul] using
                  (Real.smul_iSup_of_nonpos (a := α) hα'
                    (f := fun P : IntervalPartition a b => lowerDarbouxSum f P)).symm
          _ = α * lowerDarbouxIntegral f a b := by
                change
                  α * iSup (fun P : IntervalPartition a b => lowerDarbouxSum f P) =
                    α * sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P))
                exact (congrArg (fun x => α * x)
                  (sSup_range (f := fun P : IntervalPartition a b => lowerDarbouxSum f P))).symm
      have hEq_αf :
          lowerDarbouxIntegral (fun x => α * f x) a b =
            upperDarbouxIntegral (fun x => α * f x) a b := by
        calc
          lowerDarbouxIntegral (fun x => α * f x) a b =
              α * upperDarbouxIntegral f a b := hLowerInt
          _ = α * lowerDarbouxIntegral f a b := by
              simp [hEq_f.symm]
          _ = upperDarbouxIntegral (fun x => α * f x) a b := by
              simp [hUpperInt]
      have hαf : RiemannIntegrableOn (fun x => α * f x) a b := ⟨hbound_αf, hEq_αf⟩
      refine ⟨hαf, ?_⟩
      simp [riemannIntegral, hLowerInt, hEq_f]
  · by_cases hab : a ≤ b
    · rcases hf with ⟨hbound_f, hEq_f⟩
      rcases hg with ⟨hbound_g, hEq_g⟩
      rcases hbound_f with ⟨Mf, hMf⟩
      rcases hbound_g with ⟨Mg, hMg⟩
      have hbound_f' : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := ⟨Mf, hMf⟩
      have hbound_g' : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M := ⟨Mg, hMg⟩
      have hmin_f : ∀ x ∈ Set.Icc a b, -Mf ≤ f x := by
        intro x hx
        exact (abs_le.mp (hMf x hx)).1
      have hmax_f : ∀ x ∈ Set.Icc a b, f x ≤ Mf := by
        intro x hx
        exact (abs_le.mp (hMf x hx)).2
      have hmin_g : ∀ x ∈ Set.Icc a b, -Mg ≤ g x := by
        intro x hx
        exact (abs_le.mp (hMg x hx)).1
      have hmax_g : ∀ x ∈ Set.Icc a b, g x ≤ Mg := by
        intro x hx
        exact (abs_le.mp (hMg x hx)).2
      have subinterval_subset (P : IntervalPartition a b) (i : Fin P.n) :
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
      have lowerTag_add (P : IntervalPartition a b) (i : Fin P.n) :
          lowerTag (fun x => f x + g x) P i ≥ lowerTag f P i + lowerTag g P i := by
        have hnonempty :
            ((fun x => f x + g x) ''
              Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
          have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
            le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
          refine ⟨f (P.points (Fin.castSucc i)) + g (P.points (Fin.castSucc i)), ?_⟩
          exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
        have hlow_f :
            ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
              lowerTag f P i ≤ f x := by
          intro x hx
          have hbdd : BddBelow (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
            refine ⟨-Mf, ?_⟩
            intro y hy
            rcases hy with ⟨x', hx', rfl⟩
            exact hmin_f x' (subinterval_subset P i hx')
          have hxmem :
              f x ∈ f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
            ⟨x, hx, rfl⟩
          simpa [lowerTag] using (csInf_le hbdd hxmem)
        have hlow_g :
            ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
              lowerTag g P i ≤ g x := by
          intro x hx
          have hbdd : BddBelow (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
            refine ⟨-Mg, ?_⟩
            intro y hy
            rcases hy with ⟨x', hx', rfl⟩
            exact hmin_g x' (subinterval_subset P i hx')
          have hxmem :
              g x ∈ g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
            ⟨x, hx, rfl⟩
          simpa [lowerTag] using (csInf_le hbdd hxmem)
        refine le_csInf hnonempty ?_
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact add_le_add (hlow_f x hx) (hlow_g x hx)
      have upperTag_add (P : IntervalPartition a b) (i : Fin P.n) :
          upperTag (fun x => f x + g x) P i ≤ upperTag f P i + upperTag g P i := by
        have hnonempty :
            ((fun x => f x + g x) ''
              Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
          have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
            le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
          refine ⟨f (P.points (Fin.castSucc i)) + g (P.points (Fin.castSucc i)), ?_⟩
          exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
        have hupp_f :
            ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
              f x ≤ upperTag f P i := by
          intro x hx
          have hbdd : BddAbove (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
            refine ⟨Mf, ?_⟩
            intro y hy
            rcases hy with ⟨x', hx', rfl⟩
            exact hmax_f x' (subinterval_subset P i hx')
          have hxmem :
              f x ∈ f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
            ⟨x, hx, rfl⟩
          simpa [upperTag] using (le_csSup hbdd hxmem)
        have hupp_g :
            ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
              g x ≤ upperTag g P i := by
          intro x hx
          have hbdd : BddAbove (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
            refine ⟨Mg, ?_⟩
            intro y hy
            rcases hy with ⟨x', hx', rfl⟩
            exact hmax_g x' (subinterval_subset P i hx')
          have hxmem :
              g x ∈ g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
            ⟨x, hx, rfl⟩
          simpa [upperTag] using (le_csSup hbdd hxmem)
        refine csSup_le hnonempty ?_
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact add_le_add (hupp_f x hx) (hupp_g x hx)
      have lowerSum_add (P : IntervalPartition a b) :
          lowerDarbouxSum f P + lowerDarbouxSum g P ≤
            lowerDarbouxSum (fun x => f x + g x) P := by
        have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
          refine sub_nonneg.mpr ?_
          exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        calc
          lowerDarbouxSum f P + lowerDarbouxSum g P
              = ∑ i : Fin P.n,
                  (lowerTag f P i * P.delta i + lowerTag g P i * P.delta i) := by
                    symm
                    simpa using
                      (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin P.n)))
                        (f := fun i => lowerTag f P i * P.delta i)
                        (g := fun i => lowerTag g P i * P.delta i))
          _ = ∑ i : Fin P.n, (lowerTag f P i + lowerTag g P i) * P.delta i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
          _ ≤ ∑ i : Fin P.n, lowerTag (fun x => f x + g x) P i * P.delta i := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hle := lowerTag_add P i
                exact mul_le_mul_of_nonneg_right hle (hdelta_nonneg i)
          _ = lowerDarbouxSum (fun x => f x + g x) P := by
                rfl
      have upperSum_add (P : IntervalPartition a b) :
          upperDarbouxSum (fun x => f x + g x) P ≤
            upperDarbouxSum f P + upperDarbouxSum g P := by
        have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
          refine sub_nonneg.mpr ?_
          exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        calc
          upperDarbouxSum (fun x => f x + g x) P
              = ∑ i : Fin P.n, upperTag (fun x => f x + g x) P i * P.delta i := by
                    rfl
          _ ≤ ∑ i : Fin P.n, (upperTag f P i + upperTag g P i) * P.delta i := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hle := upperTag_add P i
                exact mul_le_mul_of_nonneg_right hle (hdelta_nonneg i)
          _ = ∑ i : Fin P.n,
                (upperTag f P i * P.delta i + upperTag g P i * P.delta i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
          _ = upperDarbouxSum f P + upperDarbouxSum g P := by
                simpa using
                  (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin P.n)))
                    (f := fun i => upperTag f P i * P.delta i)
                    (g := fun i => upperTag g P i * P.delta i))
      set Mfg : ℝ := Mf + Mg with hMfg_eq
      have hMfg : ∀ x ∈ Set.Icc a b, |f x + g x| ≤ Mfg := by
        intro x hx
        have hf' := hMf x hx
        have hg' := hMg x hx
        have hsum : |f x + g x| ≤ |f x| + |g x| := by
          simpa using (abs_add_le (f x) (g x))
        have hsum' : |f x| + |g x| ≤ Mf + Mg := add_le_add hf' hg'
        exact le_trans hsum (by simpa [hMfg_eq] using hsum')
      have hmin_fg : ∀ x ∈ Set.Icc a b, -Mfg ≤ f x + g x := by
        intro x hx
        exact (abs_le.mp (hMfg x hx)).1
      have hmax_fg : ∀ x ∈ Set.Icc a b, f x + g x ≤ Mfg := by
        intro x hx
        exact (abs_le.mp (hMfg x hx)).2
      have hBddAbove_fg :
          BddAbove (Set.range (fun P : IntervalPartition a b =>
            lowerDarbouxSum (fun x => f x + g x) P)) := by
        refine ⟨Mfg * (b - a), ?_⟩
        intro y hy
        rcases hy with ⟨P, rfl⟩
        have hsum :=
          lower_upper_sum_bounds (f := fun x => f x + g x) (a := a) (b := b) (m := -Mfg)
            (M := Mfg) hmin_fg hmax_fg P
        exact le_trans hsum.2.1 hsum.2.2
      have hBddBelow_fg :
          BddBelow (Set.range (fun P : IntervalPartition a b =>
            upperDarbouxSum (fun x => f x + g x) P)) := by
        refine ⟨(-Mfg) * (b - a), ?_⟩
        intro y hy
        rcases hy with ⟨P, rfl⟩
        have hsum :=
          lower_upper_sum_bounds (f := fun x => f x + g x) (a := a) (b := b) (m := -Mfg)
            (M := Mfg) hmin_fg hmax_fg P
        exact le_trans hsum.1 hsum.2.1
      have hlower_ge :
          lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b ≤
            lowerDarbouxIntegral (fun x => f x + g x) a b := by
        by_contra hlt
        set A : ℝ := lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b
        set B : ℝ := lowerDarbouxIntegral (fun x => f x + g x) a b
        have hlt' : B < A := lt_of_not_ge hlt
        set ε : ℝ := (A - B) / 2
        have hεpos : 0 < ε := by
          have hεpos' : 0 < (A - B) / 2 := by linarith [hlt']
          simpa [ε] using hεpos'
        have hnonempty_f :
            (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)).Nonempty := by
          obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
          refine ⟨lowerDarbouxSum f P0, ?_⟩
          exact ⟨P0, rfl⟩
        have hnonempty_g :
            (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)).Nonempty := by
          obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
          refine ⟨lowerDarbouxSum g P0, ?_⟩
          exact ⟨P0, rfl⟩
        have hlt1 :
            lowerDarbouxIntegral f a b - ε / 2 <
              sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
          have hlt1' : lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxIntegral f a b := by
            linarith [hεpos]
          simpa [lowerDarbouxIntegral] using hlt1'
        obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_lt_csSup hnonempty_f hlt1
        have hlt2 :
            lowerDarbouxIntegral g a b - ε / 2 <
              sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)) := by
          have hlt2' : lowerDarbouxIntegral g a b - ε / 2 < lowerDarbouxIntegral g a b := by
            linarith [hεpos]
          simpa [lowerDarbouxIntegral] using hlt2'
        obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_lt_csSup hnonempty_g hlt2
        rcases intervalPartition_common_refinement (a := a) (b := b) P1 P2 with
          ⟨Q, hP1Q, hP2Q⟩
        have hle1 : lowerDarbouxSum f P1 ≤ lowerDarbouxSum f Q := by
          exact (lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound_f' hP1Q).1
        have hle2 : lowerDarbouxSum g P2 ≤ lowerDarbouxSum g Q := by
          exact (lower_upper_sum_refinement (f := g) (a := a) (b := b) hbound_g' hP2Q).1
        have hsum_gt' :
            A - ε < lowerDarbouxSum f Q + lowerDarbouxSum g Q := by
          have hP1' : lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxSum f Q :=
            lt_of_lt_of_le hP1 hle1
          have hP2' : lowerDarbouxIntegral g a b - ε / 2 < lowerDarbouxSum g Q :=
            lt_of_lt_of_le hP2 hle2
          have hsum' :
              (lowerDarbouxIntegral f a b - ε / 2) +
                  (lowerDarbouxIntegral g a b - ε / 2) <
                lowerDarbouxSum f Q + lowerDarbouxSum g Q := add_lt_add hP1' hP2'
          linarith [hsum']
        have hsum_gt :
            A - ε < lowerDarbouxSum (fun x => f x + g x) Q :=
          lt_of_lt_of_le hsum_gt' (lowerSum_add Q)
        have hmem :
            lowerDarbouxSum (fun x => f x + g x) Q ∈
              Set.range (fun P : IntervalPartition a b =>
                lowerDarbouxSum (fun x => f x + g x) P) := by
          exact ⟨Q, rfl⟩
        have hle_sup :
            lowerDarbouxSum (fun x => f x + g x) Q ≤ B := by
          have hle' := le_csSup hBddAbove_fg hmem
          simpa [B, lowerDarbouxIntegral] using hle'
        have hlt'' : A - ε < B := lt_of_lt_of_le hsum_gt hle_sup
        have hgt : B < A - ε := by
          have hgt' : B < A - (A - B) / 2 := by linarith [hlt']
          simpa [ε] using hgt'
        linarith
      have hupper_le :
          upperDarbouxIntegral (fun x => f x + g x) a b ≤
            upperDarbouxIntegral f a b + upperDarbouxIntegral g a b := by
        by_contra hlt
        set A : ℝ := upperDarbouxIntegral f a b + upperDarbouxIntegral g a b
        set B : ℝ := upperDarbouxIntegral (fun x => f x + g x) a b
        have hlt' : A < B := lt_of_not_ge hlt
        set ε : ℝ := (B - A) / 2
        have hεpos : 0 < ε := by
          have hεpos' : 0 < (B - A) / 2 := by linarith [hlt']
          simpa [ε] using hεpos'
        have hnonempty_f :
            (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)).Nonempty := by
          obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
          refine ⟨upperDarbouxSum f P0, ?_⟩
          exact ⟨P0, rfl⟩
        have hnonempty_g :
            (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)).Nonempty := by
          obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
          refine ⟨upperDarbouxSum g P0, ?_⟩
          exact ⟨P0, rfl⟩
        have hlt1 :
            sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) <
              upperDarbouxIntegral f a b + ε / 2 := by
          have hlt1' : upperDarbouxIntegral f a b < upperDarbouxIntegral f a b + ε / 2 := by
            linarith [hεpos]
          simpa [upperDarbouxIntegral] using hlt1'
        obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_csInf_lt hnonempty_f hlt1
        have hlt2 :
            sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)) <
              upperDarbouxIntegral g a b + ε / 2 := by
          have hlt2' : upperDarbouxIntegral g a b < upperDarbouxIntegral g a b + ε / 2 := by
            linarith [hεpos]
          simpa [upperDarbouxIntegral] using hlt2'
        obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_csInf_lt hnonempty_g hlt2
        rcases intervalPartition_common_refinement (a := a) (b := b) P1 P2 with
          ⟨Q, hP1Q, hP2Q⟩
        have hle1 : upperDarbouxSum f Q ≤ upperDarbouxSum f P1 := by
          exact (lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound_f' hP1Q).2
        have hle2 : upperDarbouxSum g Q ≤ upperDarbouxSum g P2 := by
          exact (lower_upper_sum_refinement (f := g) (a := a) (b := b) hbound_g' hP2Q).2
        have hsum_lt' : upperDarbouxSum f Q + upperDarbouxSum g Q < A + ε := by
          have hP1' : upperDarbouxSum f Q < upperDarbouxIntegral f a b + ε / 2 :=
            lt_of_le_of_lt hle1 hP1
          have hP2' : upperDarbouxSum g Q < upperDarbouxIntegral g a b + ε / 2 :=
            lt_of_le_of_lt hle2 hP2
          have hsum' :
              upperDarbouxSum f Q + upperDarbouxSum g Q <
                (upperDarbouxIntegral f a b + ε / 2) +
                  (upperDarbouxIntegral g a b + ε / 2) := add_lt_add hP1' hP2'
          linarith [hsum']
        have hsum_lt :
            upperDarbouxSum (fun x => f x + g x) Q < A + ε :=
          lt_of_le_of_lt (upperSum_add Q) hsum_lt'
        have hmem :
            upperDarbouxSum (fun x => f x + g x) Q ∈
              Set.range (fun P : IntervalPartition a b =>
                upperDarbouxSum (fun x => f x + g x) P) := by
          exact ⟨Q, rfl⟩
        have hle_inf : B ≤ upperDarbouxSum (fun x => f x + g x) Q := by
          have hle' := csInf_le hBddBelow_fg hmem
          simpa [B, upperDarbouxIntegral] using hle'
        have hlt'' : B < A + ε := lt_of_le_of_lt hle_inf hsum_lt
        have hgt : A + ε < B := by
          have hgt' : A + (B - A) / 2 < B := by linarith [hlt']
          simpa [ε] using hgt'
        linarith
      have hle_fg :
          lowerDarbouxIntegral (fun x => f x + g x) a b ≤
            upperDarbouxIntegral (fun x => f x + g x) a b := by
        have hbounds_fg :=
          lower_upper_integral_bounds (f := fun x => f x + g x) (a := a) (b := b)
            (m := -Mfg) (M := Mfg) hab hmin_fg hmax_fg
        exact hbounds_fg.2.1
      have hge_fg :
          upperDarbouxIntegral (fun x => f x + g x) a b ≤
            lowerDarbouxIntegral (fun x => f x + g x) a b := by
        calc
          upperDarbouxIntegral (fun x => f x + g x) a b
              ≤ upperDarbouxIntegral f a b + upperDarbouxIntegral g a b := hupper_le
          _ = lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
              simp [hEq_f.symm, hEq_g.symm]
          _ ≤ lowerDarbouxIntegral (fun x => f x + g x) a b := hlower_ge
      have hEq_fg :
          lowerDarbouxIntegral (fun x => f x + g x) a b =
            upperDarbouxIntegral (fun x => f x + g x) a b := by
        exact le_antisymm hle_fg hge_fg
      have hfg : RiemannIntegrableOn (fun x => f x + g x) a b := ⟨⟨Mfg, hMfg⟩, hEq_fg⟩
      have hsum_eq :
          lowerDarbouxIntegral (fun x => f x + g x) a b =
            lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
        have hsum_le :
            lowerDarbouxIntegral (fun x => f x + g x) a b ≤
              lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
          calc
            lowerDarbouxIntegral (fun x => f x + g x) a b =
                upperDarbouxIntegral (fun x => f x + g x) a b := hEq_fg
            _ ≤ upperDarbouxIntegral f a b + upperDarbouxIntegral g a b := hupper_le
            _ = lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
                simp [hEq_f.symm, hEq_g.symm]
        exact le_antisymm hsum_le hlower_ge
      refine ⟨hfg, ?_⟩
      simp [riemannIntegral, hsum_eq]
    · have hbound_fg : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x + g x| ≤ M := by
        refine ⟨0, ?_⟩
        intro x hx
        have : a ≤ b := le_trans hx.1 hx.2
        exact (hab this).elim
      have hno_lower (f' : ℝ → ℝ) :
          (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f' P)) = ∅ := by
        ext y
        constructor
        · rintro ⟨P, rfl⟩
          have hmono : Monotone P.points := P.mono.monotone
          have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
          have hPab : a ≤ b := by
            simpa [P.left_eq, P.right_eq, Fin.last] using h0
          exact (hab hPab).elim
        · intro hy
          cases hy
      have hno_upper (f' : ℝ → ℝ) :
          (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f' P)) = ∅ := by
        ext y
        constructor
        · rintro ⟨P, rfl⟩
          have hmono : Monotone P.points := P.mono.monotone
          have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
          have hPab : a ≤ b := by
            simpa [P.left_eq, P.right_eq, Fin.last] using h0
          exact (hab hPab).elim
        · intro hy
          cases hy
      have hEq_fg :
          lowerDarbouxIntegral (fun x => f x + g x) a b =
            upperDarbouxIntegral (fun x => f x + g x) a b := by
        simp [lowerDarbouxIntegral, upperDarbouxIntegral, hno_lower, hno_upper]
      have hfg : RiemannIntegrableOn (fun x => f x + g x) a b := ⟨hbound_fg, hEq_fg⟩
      refine ⟨hfg, ?_⟩
      simp [riemannIntegral, lowerDarbouxIntegral, hno_lower]

/-- Proposition 5.2.5: Let bounded functions `f, g : [a, b] → ℝ`. Then the
upper Darboux integral of their sum is at most the sum of their upper Darboux
integrals, and the lower Darboux integral of their sum is at least the sum of
their lower Darboux integrals. -/
lemma darbouxIntegral_add_le_add {a b : ℝ} {f g : ℝ → ℝ}
    (hbound_f : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hbound_g : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    upperDarbouxIntegral (fun x => f x + g x) a b ≤
        upperDarbouxIntegral f a b + upperDarbouxIntegral g a b ∧
      lowerDarbouxIntegral (fun x => f x + g x) a b ≥
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
  classical
  by_cases hab : a ≤ b
  · rcases hbound_f with ⟨Mf, hMf⟩
    rcases hbound_g with ⟨Mg, hMg⟩
    have hbound_f' : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := ⟨Mf, hMf⟩
    have hbound_g' : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M := ⟨Mg, hMg⟩
    have hmin_f : ∀ x ∈ Set.Icc a b, -Mf ≤ f x := by
      intro x hx
      exact (abs_le.mp (hMf x hx)).1
    have hmax_f : ∀ x ∈ Set.Icc a b, f x ≤ Mf := by
      intro x hx
      exact (abs_le.mp (hMf x hx)).2
    have hmin_g : ∀ x ∈ Set.Icc a b, -Mg ≤ g x := by
      intro x hx
      exact (abs_le.mp (hMg x hx)).1
    have hmax_g : ∀ x ∈ Set.Icc a b, g x ≤ Mg := by
      intro x hx
      exact (abs_le.mp (hMg x hx)).2
    have subinterval_subset (P : IntervalPartition a b) (i : Fin P.n) :
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
    have lowerTag_add (P : IntervalPartition a b) (i : Fin P.n) :
        lowerTag (fun x => f x + g x) P i ≥ lowerTag f P i + lowerTag g P i := by
      have hnonempty :
          ((fun x => f x + g x) ''
            Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
        have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
          le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        refine ⟨f (P.points (Fin.castSucc i)) + g (P.points (Fin.castSucc i)), ?_⟩
        exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
      have hlow_f :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            lowerTag f P i ≤ f x := by
        intro x hx
        have hbdd : BddBelow (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨-Mf, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmin_f x' (subinterval_subset P i hx')
        have hxmem :
            f x ∈ f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        simpa [lowerTag] using (csInf_le hbdd hxmem)
      have hlow_g :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            lowerTag g P i ≤ g x := by
        intro x hx
        have hbdd : BddBelow (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨-Mg, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmin_g x' (subinterval_subset P i hx')
        have hxmem :
            g x ∈ g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        simpa [lowerTag] using (csInf_le hbdd hxmem)
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact add_le_add (hlow_f x hx) (hlow_g x hx)
    have upperTag_add (P : IntervalPartition a b) (i : Fin P.n) :
        upperTag (fun x => f x + g x) P i ≤ upperTag f P i + upperTag g P i := by
      have hnonempty :
          ((fun x => f x + g x) ''
            Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
        have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
          le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        refine ⟨f (P.points (Fin.castSucc i)) + g (P.points (Fin.castSucc i)), ?_⟩
        exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
      have hupp_f :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            f x ≤ upperTag f P i := by
        intro x hx
        have hbdd : BddAbove (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨Mf, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmax_f x' (subinterval_subset P i hx')
        have hxmem :
            f x ∈ f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        simpa [upperTag] using (le_csSup hbdd hxmem)
      have hupp_g :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            g x ≤ upperTag g P i := by
        intro x hx
        have hbdd : BddAbove (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨Mg, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmax_g x' (subinterval_subset P i hx')
        have hxmem :
            g x ∈ g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        simpa [upperTag] using (le_csSup hbdd hxmem)
      refine csSup_le hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact add_le_add (hupp_f x hx) (hupp_g x hx)
    have lowerSum_add (P : IntervalPartition a b) :
        lowerDarbouxSum f P + lowerDarbouxSum g P ≤
          lowerDarbouxSum (fun x => f x + g x) P := by
      have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
        refine sub_nonneg.mpr ?_
        exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
      calc
        lowerDarbouxSum f P + lowerDarbouxSum g P
            = ∑ i : Fin P.n,
                (lowerTag f P i * P.delta i + lowerTag g P i * P.delta i) := by
                  symm
                  simpa using
                    (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin P.n)))
                      (f := fun i => lowerTag f P i * P.delta i)
                      (g := fun i => lowerTag g P i * P.delta i))
        _ = ∑ i : Fin P.n, (lowerTag f P i + lowerTag g P i) * P.delta i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ ≤ ∑ i : Fin P.n, lowerTag (fun x => f x + g x) P i * P.delta i := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hle := lowerTag_add P i
              exact mul_le_mul_of_nonneg_right hle (hdelta_nonneg i)
        _ = lowerDarbouxSum (fun x => f x + g x) P := by
              rfl
    have upperSum_add (P : IntervalPartition a b) :
        upperDarbouxSum (fun x => f x + g x) P ≤
          upperDarbouxSum f P + upperDarbouxSum g P := by
      have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
        refine sub_nonneg.mpr ?_
        exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
      calc
        upperDarbouxSum (fun x => f x + g x) P
            = ∑ i : Fin P.n, upperTag (fun x => f x + g x) P i * P.delta i := by
                  rfl
        _ ≤ ∑ i : Fin P.n, (upperTag f P i + upperTag g P i) * P.delta i := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hle := upperTag_add P i
              exact mul_le_mul_of_nonneg_right hle (hdelta_nonneg i)
        _ = ∑ i : Fin P.n,
              (upperTag f P i * P.delta i + upperTag g P i * P.delta i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = upperDarbouxSum f P + upperDarbouxSum g P := by
              simpa using
                (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin P.n)))
                  (f := fun i => upperTag f P i * P.delta i)
                  (g := fun i => upperTag g P i * P.delta i))
    set Mfg : ℝ := Mf + Mg with hMfg_eq
    have hMfg : ∀ x ∈ Set.Icc a b, |f x + g x| ≤ Mfg := by
      intro x hx
      have hf' := hMf x hx
      have hg' := hMg x hx
      have hsum : |f x + g x| ≤ |f x| + |g x| := by
        simpa using (abs_add_le (f x) (g x))
      have hsum' : |f x| + |g x| ≤ Mf + Mg := add_le_add hf' hg'
      exact le_trans hsum (by simpa [hMfg_eq] using hsum')
    have hmin_fg : ∀ x ∈ Set.Icc a b, -Mfg ≤ f x + g x := by
      intro x hx
      exact (abs_le.mp (hMfg x hx)).1
    have hmax_fg : ∀ x ∈ Set.Icc a b, f x + g x ≤ Mfg := by
      intro x hx
      exact (abs_le.mp (hMfg x hx)).2
    have hBddAbove_fg :
        BddAbove (Set.range (fun P : IntervalPartition a b =>
          lowerDarbouxSum (fun x => f x + g x) P)) := by
      refine ⟨Mfg * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := fun x => f x + g x) (a := a) (b := b) (m := -Mfg)
          (M := Mfg) hmin_fg hmax_fg P
      exact le_trans hsum.2.1 hsum.2.2
    have hBddBelow_fg :
        BddBelow (Set.range (fun P : IntervalPartition a b =>
          upperDarbouxSum (fun x => f x + g x) P)) := by
      refine ⟨(-Mfg) * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := fun x => f x + g x) (a := a) (b := b) (m := -Mfg)
          (M := Mfg) hmin_fg hmax_fg P
      exact le_trans hsum.1 hsum.2.1
    have hlower_ge :
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b ≤
          lowerDarbouxIntegral (fun x => f x + g x) a b := by
      by_contra hlt
      set A : ℝ := lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b
      set B : ℝ := lowerDarbouxIntegral (fun x => f x + g x) a b
      have hlt' : B < A := lt_of_not_ge hlt
      set ε : ℝ := (A - B) / 2
      have hεpos : 0 < ε := by
        have hεpos' : 0 < (A - B) / 2 := by linarith [hlt']
        simpa [ε] using hεpos'
      have hnonempty_f :
          (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)).Nonempty := by
        obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
        refine ⟨lowerDarbouxSum f P0, ?_⟩
        exact ⟨P0, rfl⟩
      have hnonempty_g :
          (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)).Nonempty := by
        obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
        refine ⟨lowerDarbouxSum g P0, ?_⟩
        exact ⟨P0, rfl⟩
      have hlt1 :
          lowerDarbouxIntegral f a b - ε / 2 <
            sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
        have hlt1' : lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxIntegral f a b := by
          linarith [hεpos]
        simpa [lowerDarbouxIntegral] using hlt1'
      obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_lt_csSup hnonempty_f hlt1
      have hlt2 :
          lowerDarbouxIntegral g a b - ε / 2 <
            sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)) := by
        have hlt2' : lowerDarbouxIntegral g a b - ε / 2 < lowerDarbouxIntegral g a b := by
          linarith [hεpos]
        simpa [lowerDarbouxIntegral] using hlt2'
      obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_lt_csSup hnonempty_g hlt2
      rcases intervalPartition_common_refinement (a := a) (b := b) P1 P2 with
        ⟨Q, hP1Q, hP2Q⟩
      have hle1 : lowerDarbouxSum f P1 ≤ lowerDarbouxSum f Q := by
        exact (lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound_f' hP1Q).1
      have hle2 : lowerDarbouxSum g P2 ≤ lowerDarbouxSum g Q := by
        exact (lower_upper_sum_refinement (f := g) (a := a) (b := b) hbound_g' hP2Q).1
      have hsum_gt' :
          A - ε < lowerDarbouxSum f Q + lowerDarbouxSum g Q := by
        have hP1' : lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxSum f Q :=
          lt_of_lt_of_le hP1 hle1
        have hP2' : lowerDarbouxIntegral g a b - ε / 2 < lowerDarbouxSum g Q :=
          lt_of_lt_of_le hP2 hle2
        have hsum' :
            (lowerDarbouxIntegral f a b - ε / 2) +
                (lowerDarbouxIntegral g a b - ε / 2) <
              lowerDarbouxSum f Q + lowerDarbouxSum g Q := add_lt_add hP1' hP2'
        linarith [hsum']
      have hsum_gt :
          A - ε < lowerDarbouxSum (fun x => f x + g x) Q :=
        lt_of_lt_of_le hsum_gt' (lowerSum_add Q)
      have hmem :
          lowerDarbouxSum (fun x => f x + g x) Q ∈
            Set.range (fun P : IntervalPartition a b =>
              lowerDarbouxSum (fun x => f x + g x) P) := by
        exact ⟨Q, rfl⟩
      have hle_sup :
          lowerDarbouxSum (fun x => f x + g x) Q ≤ B := by
        have hle' := le_csSup hBddAbove_fg hmem
        simpa [B, lowerDarbouxIntegral] using hle'
      have hlt'' : A - ε < B := lt_of_lt_of_le hsum_gt hle_sup
      have hgt : B < A - ε := by
        have hgt' : B < A - (A - B) / 2 := by linarith [hlt']
        simpa [ε] using hgt'
      linarith
    have hupper_le :
        upperDarbouxIntegral (fun x => f x + g x) a b ≤
          upperDarbouxIntegral f a b + upperDarbouxIntegral g a b := by
      by_contra hlt
      set A : ℝ := upperDarbouxIntegral f a b + upperDarbouxIntegral g a b
      set B : ℝ := upperDarbouxIntegral (fun x => f x + g x) a b
      have hlt' : A < B := lt_of_not_ge hlt
      set ε : ℝ := (B - A) / 2
      have hεpos : 0 < ε := by
        have hεpos' : 0 < (B - A) / 2 := by linarith [hlt']
        simpa [ε] using hεpos'
      have hnonempty_f :
          (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)).Nonempty := by
        obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
        refine ⟨upperDarbouxSum f P0, ?_⟩
        exact ⟨P0, rfl⟩
      have hnonempty_g :
          (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)).Nonempty := by
        obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
        refine ⟨upperDarbouxSum g P0, ?_⟩
        exact ⟨P0, rfl⟩
      have hlt1 :
          sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) <
            upperDarbouxIntegral f a b + ε / 2 := by
        have hlt1' : upperDarbouxIntegral f a b < upperDarbouxIntegral f a b + ε / 2 := by
          linarith [hεpos]
        simpa [upperDarbouxIntegral] using hlt1'
      obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_csInf_lt hnonempty_f hlt1
      have hlt2 :
          sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)) <
            upperDarbouxIntegral g a b + ε / 2 := by
        have hlt2' : upperDarbouxIntegral g a b < upperDarbouxIntegral g a b + ε / 2 := by
          linarith [hεpos]
        simpa [upperDarbouxIntegral] using hlt2'
      obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_csInf_lt hnonempty_g hlt2
      rcases intervalPartition_common_refinement (a := a) (b := b) P1 P2 with
        ⟨Q, hP1Q, hP2Q⟩
      have hle1 : upperDarbouxSum f Q ≤ upperDarbouxSum f P1 := by
        exact (lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound_f' hP1Q).2
      have hle2 : upperDarbouxSum g Q ≤ upperDarbouxSum g P2 := by
        exact (lower_upper_sum_refinement (f := g) (a := a) (b := b) hbound_g' hP2Q).2
      have hsum_lt' : upperDarbouxSum f Q + upperDarbouxSum g Q < A + ε := by
        have hP1' : upperDarbouxSum f Q < upperDarbouxIntegral f a b + ε / 2 :=
          lt_of_le_of_lt hle1 hP1
        have hP2' : upperDarbouxSum g Q < upperDarbouxIntegral g a b + ε / 2 :=
          lt_of_le_of_lt hle2 hP2
        have hsum' :
            upperDarbouxSum f Q + upperDarbouxSum g Q <
              (upperDarbouxIntegral f a b + ε / 2) +
                (upperDarbouxIntegral g a b + ε / 2) := add_lt_add hP1' hP2'
        linarith [hsum']
      have hsum_lt :
          upperDarbouxSum (fun x => f x + g x) Q < A + ε :=
        lt_of_le_of_lt (upperSum_add Q) hsum_lt'
      have hmem :
          upperDarbouxSum (fun x => f x + g x) Q ∈
            Set.range (fun P : IntervalPartition a b =>
              upperDarbouxSum (fun x => f x + g x) P) := by
        exact ⟨Q, rfl⟩
      have hle_inf : B ≤ upperDarbouxSum (fun x => f x + g x) Q := by
        have hle' := csInf_le hBddBelow_fg hmem
        simpa [B, upperDarbouxIntegral] using hle'
      have hlt'' : B < A + ε := lt_of_le_of_lt hle_inf hsum_lt
      have hgt : A + ε < B := by
        have hgt' : A + (B - A) / 2 < B := by linarith [hlt']
        simpa [ε] using hgt'
      linarith
    exact ⟨hupper_le, hlower_ge⟩
  · have hno_lower (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hno_upper (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hupper :
        upperDarbouxIntegral (fun x => f x + g x) a b ≤
          upperDarbouxIntegral f a b + upperDarbouxIntegral g a b := by
      simp [upperDarbouxIntegral, hno_upper]
    have hlower :
        lowerDarbouxIntegral (fun x => f x + g x) a b ≥
          lowerDarbouxIntegral f a b + lowerDarbouxIntegral g a b := by
      simp [lowerDarbouxIntegral, hno_lower]
    exact ⟨hupper, hlower⟩

/-- Proposition 5.2.6 (Monotonicity): If bounded functions `f, g : [a, b] → ℝ`
satisfy `f x ≤ g x` on `[a, b]`, then their lower and upper Darboux integrals
obey `∫̲_a^b f ≤ ∫̲_a^b g` and `∫̅_a^b f ≤ ∫̅_a^b g`. Moreover, if `f` and `g`
are Riemann integrable on `[a, b]`, then `∫_a^b f ≤ ∫_a^b g`. -/
lemma darbouxIntegral_monotone {a b : ℝ} {f g : ℝ → ℝ}
    (hbound_f : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hbound_g : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (hmono : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    lowerDarbouxIntegral f a b ≤ lowerDarbouxIntegral g a b ∧
      upperDarbouxIntegral f a b ≤ upperDarbouxIntegral g a b := by
  classical
  by_cases hab : a ≤ b
  · rcases hbound_f with ⟨Mf, hMf⟩
    rcases hbound_g with ⟨Mg, hMg⟩
    have hmin_f : ∀ x ∈ Set.Icc a b, -Mf ≤ f x := by
      intro x hx
      exact (abs_le.mp (hMf x hx)).1
    have hmax_f : ∀ x ∈ Set.Icc a b, f x ≤ Mf := by
      intro x hx
      exact (abs_le.mp (hMf x hx)).2
    have hmin_g : ∀ x ∈ Set.Icc a b, -Mg ≤ g x := by
      intro x hx
      exact (abs_le.mp (hMg x hx)).1
    have hmax_g : ∀ x ∈ Set.Icc a b, g x ≤ Mg := by
      intro x hx
      exact (abs_le.mp (hMg x hx)).2
    have subinterval_subset (P : IntervalPartition a b) (i : Fin P.n) :
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
    have lowerTag_le (P : IntervalPartition a b) (i : Fin P.n) :
        lowerTag f P i ≤ lowerTag g P i := by
      have hnonempty :
          (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
        have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
          le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        refine ⟨g (P.points (Fin.castSucc i)), ?_⟩
        exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
      have hlow_f :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            lowerTag f P i ≤ f x := by
        intro x hx
        have hbdd : BddBelow (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨-Mf, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmin_f x' (subinterval_subset P i hx')
        have hxmem :
            f x ∈ f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        simpa [lowerTag] using (csInf_le hbdd hxmem)
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_trans (hlow_f x hx) (hmono x (subinterval_subset P i hx))
    have upperTag_le (P : IntervalPartition a b) (i : Fin P.n) :
        upperTag f P i ≤ upperTag g P i := by
      have hnonempty :
          (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
        have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
          le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        refine ⟨f (P.points (Fin.castSucc i)), ?_⟩
        exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
      have hupp_g :
          ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ),
            f x ≤ upperTag g P i := by
        intro x hx
        have hbdd : BddAbove (g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
          refine ⟨Mg, ?_⟩
          intro y hy
          rcases hy with ⟨x', hx', rfl⟩
          exact hmax_g x' (subinterval_subset P i hx')
        have hxmem :
            g x ∈ g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          ⟨x, hx, rfl⟩
        have hle : g x ≤ upperTag g P i := by
          simpa [upperTag] using (le_csSup hbdd hxmem)
        exact le_trans (hmono x (subinterval_subset P i hx)) hle
      refine csSup_le hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hupp_g x hx
    have lowerSum_le (P : IntervalPartition a b) :
        lowerDarbouxSum f P ≤ lowerDarbouxSum g P := by
      have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
        refine sub_nonneg.mpr ?_
        exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
      have hterm :
          ∀ i : Fin P.n, lowerTag f P i * P.delta i ≤ lowerTag g P i * P.delta i := by
        intro i
        exact mul_le_mul_of_nonneg_right (lowerTag_le P i) (hdelta_nonneg i)
      have hsum :
          (∑ i : Fin P.n, lowerTag f P i * P.delta i) ≤
            ∑ i : Fin P.n, lowerTag g P i * P.delta i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hterm i
      simpa [lowerDarbouxSum] using hsum
    have upperSum_le (P : IntervalPartition a b) :
        upperDarbouxSum f P ≤ upperDarbouxSum g P := by
      have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
        refine sub_nonneg.mpr ?_
        exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
      have hterm :
          ∀ i : Fin P.n, upperTag f P i * P.delta i ≤ upperTag g P i * P.delta i := by
        intro i
        exact mul_le_mul_of_nonneg_right (upperTag_le P i) (hdelta_nonneg i)
      have hsum :
          (∑ i : Fin P.n, upperTag f P i * P.delta i) ≤
            ∑ i : Fin P.n, upperTag g P i * P.delta i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hterm i
      simpa [upperDarbouxSum] using hsum
    have hBddAbove_g :
        BddAbove (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)) := by
      refine ⟨Mg * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := g) (a := a) (b := b) (m := -Mg) (M := Mg) hmin_g hmax_g P
      exact le_trans hsum.2.1 hsum.2.2
    have hBddBelow_f :
        BddBelow (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) := by
      refine ⟨(-Mf) * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := -Mf) (M := Mf) hmin_f hmax_f P
      exact le_trans hsum.1 hsum.2.1
    obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
    have hnonempty_lower :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)).Nonempty := by
      refine ⟨lowerDarbouxSum f P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hnonempty_upper :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)).Nonempty := by
      refine ⟨upperDarbouxSum g P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hlower : lowerDarbouxIntegral f a b ≤ lowerDarbouxIntegral g a b := by
      have hle :
          ∀ y ∈ Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P),
            y ≤ lowerDarbouxIntegral g a b := by
        intro y hy
        rcases hy with ⟨P, rfl⟩
        have hsum := lowerSum_le P
        have hmem :
            lowerDarbouxSum g P ∈
              Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P) := ⟨P, rfl⟩
        have hsup' :
            lowerDarbouxSum g P ≤
              sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P)) := by
          exact le_csSup hBddAbove_g hmem
        have hsup : lowerDarbouxSum g P ≤ lowerDarbouxIntegral g a b := by
          simpa [lowerDarbouxIntegral] using hsup'
        exact le_trans hsum hsup
      have hsup :
          sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P))
            ≤ lowerDarbouxIntegral g a b := csSup_le hnonempty_lower hle
      simpa [lowerDarbouxIntegral] using hsup
    have hupper : upperDarbouxIntegral f a b ≤ upperDarbouxIntegral g a b := by
      have hle :
          ∀ y ∈ Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P),
            upperDarbouxIntegral f a b ≤ y := by
        intro y hy
        rcases hy with ⟨P, rfl⟩
        have hsum := upperSum_le P
        have hmem :
            upperDarbouxSum f P ∈
              Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P) := ⟨P, rfl⟩
        have hinf' :
            sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P))
              ≤ upperDarbouxSum f P := by
          exact csInf_le hBddBelow_f hmem
        have hinf : upperDarbouxIntegral f a b ≤ upperDarbouxSum f P := by
          simpa [upperDarbouxIntegral] using hinf'
        exact le_trans hinf hsum
      have hle_inf :
          upperDarbouxIntegral f a b ≤
            sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P)) :=
        le_csInf hnonempty_upper hle
      simpa [upperDarbouxIntegral] using hle_inf
    exact ⟨hlower, hupper⟩
  · have hno_lower (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hno_upper (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hlower : lowerDarbouxIntegral f a b ≤ lowerDarbouxIntegral g a b := by
      simp [lowerDarbouxIntegral, hno_lower]
    have hupper : upperDarbouxIntegral f a b ≤ upperDarbouxIntegral g a b := by
      simp [upperDarbouxIntegral, hno_upper]
    exact ⟨hlower, hupper⟩

lemma riemannIntegral_monotone {a b : ℝ} {f g : ℝ → ℝ}
    (hmono : ∀ x ∈ Set.Icc a b, f x ≤ g x)
    (hf : RiemannIntegrableOn f a b) (hg : RiemannIntegrableOn g a b) :
    riemannIntegral f a b hf ≤ riemannIntegral g a b hg := by
  classical
  rcases hf with ⟨hbound_f, _⟩
  rcases hg with ⟨hbound_g, _⟩
  have hmono' :=
    darbouxIntegral_monotone (a := a) (b := b) (f := f) (g := g)
      hbound_f hbound_g hmono
  simpa [riemannIntegral] using hmono'.1

end Section02
end Chap05
