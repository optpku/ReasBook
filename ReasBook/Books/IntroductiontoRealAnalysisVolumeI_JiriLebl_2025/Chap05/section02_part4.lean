/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section02_part3

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02
/-- Lemma 5.2.7: A continuous function on a closed bounded interval `[a, b]`
belongs to `ℛ([a, b])`, i.e., it is Riemann integrable on that interval. -/
lemma continuousOn_riemannIntegrableOn {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc a b)) :
    RiemannIntegrableOn f a b := by
  classical
  by_cases hab : a ≤ b
  · have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M :=
      lemma_3_3_1 hab hcont
    have hgap : ∀ ε > 0, ∃ P : IntervalPartition a b,
        upperDarbouxSum f P - lowerDarbouxSum f P < ε := by
      intro ε hε
      by_cases hlt : a < b
      · have hbapos : 0 < b - a := sub_pos.mpr hlt
        set ε' : ℝ := ε / 2 with hε'
        have hε'pos : 0 < ε' := by
          simpa [hε'] using (half_pos hε)
        have huc : UniformContinuousOn f (Set.Icc a b) := by
          simpa using (isCompact_Icc.uniformContinuousOn_of_continuous hcont)
        obtain ⟨δ, hδpos, hδ⟩ :=
          (Metric.uniformContinuousOn_iff.1 huc) (ε' / (b - a))
            (by exact div_pos hε'pos hbapos)
        have hpos : 0 < δ / (b - a) := by
          exact div_pos hδpos hbapos
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hpos
        let N : ℕ := n + 1
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.succ_pos n)
        have hNne : (N : ℝ) ≠ 0 := by
          exact_mod_cast (show (N : ℕ) ≠ 0 by simp [N])
        have hstep_lt : (b - a) / (N : ℝ) < δ := by
          have hn' : 1 / (N : ℝ) < δ / (b - a) := by
            simpa [N] using hn
          have hmul := mul_lt_mul_of_pos_left hn' hbapos
          have hba_ne : (b - a) ≠ 0 := by linarith
          calc
            (b - a) / (N : ℝ) = (b - a) * (1 / (N : ℝ)) := by
              simp [div_eq_mul_inv, mul_comm]
            _ < (b - a) * (δ / (b - a)) := hmul
            _ = δ := by
              field_simp [hba_ne]
        let P : IntervalPartition a b :=
          { n := N
            points := fun i : Fin (N + 1) => a + (i : ℝ) * ((b - a) / (N : ℝ))
            mono := by
              refine (Fin.strictMono_iff_lt_succ (f := fun i : Fin (N + 1) =>
                a + (i : ℝ) * ((b - a) / (N : ℝ)))).2 ?_
              intro i
              have hi : (i : ℝ) < (i.succ : ℝ) := by
                exact_mod_cast (Fin.castSucc_lt_succ (i := i))
              have hstep_pos : 0 < (b - a) / (N : ℝ) := by
                exact div_pos hbapos hNpos
              have hmul : (i : ℝ) * ((b - a) / (N : ℝ)) <
                  (i.succ : ℝ) * ((b - a) / (N : ℝ)) :=
                mul_lt_mul_of_pos_right hi hstep_pos
              simpa using (add_lt_add_left hmul a)
            left_eq := by
              simp
            right_eq := by
              calc
                a + (N : ℝ) * ((b - a) / (N : ℝ)) = a + (b - a) := by
                  simp [div_eq_mul_inv, hNne, mul_left_comm]
                _ = b := by ring }
        have hdelta : ∀ i : Fin P.n, P.delta i = (b - a) / (N : ℝ) := by
          intro i
          have :
              a + ((i : ℝ) + 1) * ((b - a) / (N : ℝ)) -
                (a + (i : ℝ) * ((b - a) / (N : ℝ)))
                = (b - a) / (N : ℝ) := by
            ring
          simpa [IntervalPartition.delta, P, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
            add_assoc] using this
        have hdelta_lt : ∀ i : Fin P.n, P.delta i < δ := by
          intro i
          simpa [hdelta i] using hstep_lt
        have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
          refine sub_nonneg.mpr ?_
          exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
        have hsum_delta : (∑ i : Fin P.n, P.delta i) = b - a := by
          have sum_succ_sub_castSucc : ∀ {n : ℕ} (g : Fin (n + 1) → ℝ),
              (∑ i : Fin n, (g i.succ - g (Fin.castSucc i))) =
                g (Fin.last n) - g 0 := by
            intro n g
            induction n with
            | zero =>
                simp
            | succ n ih =>
                have hsum :=
                  (Fin.sum_univ_succ (f := fun i : Fin (n + 1) =>
                    (g i.succ - g (Fin.castSucc i))))
                have hih :
                    (∑ i : Fin n,
                        (g (i.succ).succ - g (Fin.castSucc (i.succ)))) =
                      g (Fin.last (n + 1)) - g 1 := by
                  simpa using (ih (g := fun j : Fin (n + 1) => g j.succ))
                calc
                  (∑ i : Fin (n + 1), (g i.succ - g (Fin.castSucc i)))
                      = (g (Fin.succ 0) - g (Fin.castSucc 0)) +
                          ∑ i : Fin n,
                            (g (i.succ).succ - g (Fin.castSucc (i.succ))) := hsum
                  _ = (g (Fin.succ 0) - g (Fin.castSucc 0)) +
                      (g (Fin.last (n + 1)) - g 1) := by
                        rw [hih]
                  _ = (g 1 - g 0) + (g (Fin.last (n + 1)) - g 1) := by
                        simp
                  _ = g (Fin.last (n + 1)) - g 0 := by ring
          have h := sum_succ_sub_castSucc (g := P.points)
          simpa [IntervalPartition.delta, P.left_eq, P.right_eq, Fin.last] using h
        have hsub (i : Fin P.n) :
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
        have htag_gap (i : Fin P.n) :
            upperTag f P i - lowerTag f P i ≤ ε' / (b - a) := by
          set left := P.points (Fin.castSucc i)
          set right := P.points i.succ
          have hle_lr : left ≤ right := by
            have hlt_lr : left < right := P.mono (Fin.castSucc_lt_succ (i := i))
            exact le_of_lt hlt_lr
          have hcont_sub : ContinuousOn f (Set.Icc left right) := by
            refine hcont.mono ?_
            intro x hx
            exact hsub i (by simpa [left, right] using hx)
          obtain ⟨x, hxI, hxmax⟩ := theorem_3_3_2_max_helper hle_lr hcont_sub
          obtain ⟨y, hyI, hymin⟩ := theorem_3_3_2_min_helper hle_lr hcont_sub
          have hupper : upperTag f P i = f x := by
            have hnonempty : (f '' Set.Icc left right).Nonempty := by
              exact ⟨f x, ⟨x, hxI, rfl⟩⟩
            have hbdd : BddAbove (f '' Set.Icc left right) := by
              refine ⟨f x, ?_⟩
              intro z hz
              rcases hz with ⟨z, hzI, rfl⟩
              exact hxmax z hzI
            have hle : upperTag f P i ≤ f x := by
              have hle' : sSup (f '' Set.Icc left right) ≤ f x := by
                refine csSup_le hnonempty ?_
                intro z hz
                rcases hz with ⟨z, hzI, rfl⟩
                exact hxmax z hzI
              simpa [upperTag, left, right] using hle'
            have hge : f x ≤ upperTag f P i := by
              have hge' : f x ≤ sSup (f '' Set.Icc left right) := by
                refine le_csSup hbdd ?_
                exact ⟨x, hxI, rfl⟩
              simpa [upperTag, left, right] using hge'
            exact le_antisymm hle hge
          have hlower : lowerTag f P i = f y := by
            have hnonempty : (f '' Set.Icc left right).Nonempty := by
              exact ⟨f y, ⟨y, hyI, rfl⟩⟩
            have hbdd : BddBelow (f '' Set.Icc left right) := by
              refine ⟨f y, ?_⟩
              intro z hz
              rcases hz with ⟨z, hzI, rfl⟩
              exact hymin z hzI
            have hle : f y ≤ lowerTag f P i := by
              have hle' : f y ≤ sInf (f '' Set.Icc left right) := by
                refine le_csInf hnonempty ?_
                intro z hz
                rcases hz with ⟨z, hzI, rfl⟩
                exact hymin z hzI
              simpa [lowerTag, left, right] using hle'
            have hge : lowerTag f P i ≤ f y := by
              have hge' : sInf (f '' Set.Icc left right) ≤ f y := by
                refine csInf_le hbdd ?_
                exact ⟨y, hyI, rfl⟩
              simpa [lowerTag, left, right] using hge'
            exact le_antisymm hge hle
          have hxmem : x ∈ Set.Icc a b := by
            exact hsub i (by simpa [left, right] using hxI)
          have hymem : y ∈ Set.Icc a b := by
            exact hsub i (by simpa [left, right] using hyI)
          have hxy_le : |x - y| ≤ P.delta i := by
            have h1 : x - y ≤ P.delta i := by
              have : x - y ≤ right - left := by linarith [hxI.2, hyI.1]
              simpa [IntervalPartition.delta, left, right] using this
            have h2 : y - x ≤ P.delta i := by
              have : y - x ≤ right - left := by linarith [hxI.1, hyI.2]
              simpa [IntervalPartition.delta, left, right] using this
            exact (abs_sub_le_iff).2 ⟨h1, h2⟩
          have hdist : dist x y < δ := by
            have hxy_lt : |x - y| < δ := lt_of_le_of_lt hxy_le (hdelta_lt i)
            simpa [Real.dist_eq] using hxy_lt
          have hfxfy : dist (f x) (f y) < ε' / (b - a) :=
            hδ x hxmem y hymem hdist
          have hfxfy' : |f x - f y| < ε' / (b - a) := by
            simpa [Real.dist_eq] using hfxfy
          have hle : f x - f y ≤ ε' / (b - a) := by
            have hle' : f x - f y ≤ |f x - f y| := by
              exact le_abs_self _
            exact le_trans hle' (le_of_lt hfxfy')
          simpa [hupper, hlower] using hle
        have hgap_le :
            upperDarbouxSum f P - lowerDarbouxSum f P ≤ ε' := by
          calc
            upperDarbouxSum f P - lowerDarbouxSum f P
                = ∑ i : Fin P.n,
                    (upperTag f P i * P.delta i - lowerTag f P i * P.delta i) := by
                      simp [upperDarbouxSum, lowerDarbouxSum, Finset.sum_sub_distrib]
            _ = ∑ i : Fin P.n, (upperTag f P i - lowerTag f P i) * P.delta i := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
            _ ≤ ∑ i : Fin P.n, (ε' / (b - a)) * P.delta i := by
                      refine Finset.sum_le_sum ?_
                      intro i hi
                      exact mul_le_mul_of_nonneg_right (htag_gap i) (hdelta_nonneg i)
            _ = (ε' / (b - a)) * ∑ i : Fin P.n, P.delta i := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ)
                          (f := fun i : Fin P.n => P.delta i)
                          (a := ε' / (b - a))).symm
            _ = (ε' / (b - a)) * (b - a) := by
                      simp [hsum_delta]
            _ = ε' := by
                      have hba_ne : (b - a) ≠ 0 := by linarith
                      field_simp [hba_ne]
        have hε'lt : ε' < ε := by
          have := half_lt_self hε
          simpa [hε'] using this
        refine ⟨P, lt_of_le_of_lt hgap_le hε'lt⟩
      · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
        subst hEq
        let P : IntervalPartition a a :=
          { n := 0
            points := fun _ => a
            mono := by
              refine (Fin.strictMono_iff_lt_succ (f := fun _ : Fin (0 + 1) => a)).2 ?_
              intro i
              exact (Fin.elim0 i)
            left_eq := by simp
            right_eq := by simp }
        have hgap0 : upperDarbouxSum f P - lowerDarbouxSum f P = 0 := by
          simp [upperDarbouxSum, lowerDarbouxSum, P]
        refine ⟨P, ?_⟩
        simpa [hgap0] using hε
    exact riemannIntegrable_of_upper_lower_gap hbound hgap
  · have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
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
    have hEq :
        lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
      simp [lowerDarbouxIntegral, upperDarbouxIntegral, hno_lower, hno_upper]
    exact ⟨hbound, hEq⟩

/-- Lemma 5.2.8: Let `f : [a, b] → ℝ` be bounded, and suppose sequences
`aₙ, bₙ` satisfy `a < aₙ < bₙ < b` for all `n` with `aₙ → a` and `bₙ → b`.
If `f ∈ ℛ([aₙ, bₙ])` for every `n`, then `f ∈ ℛ([a, b])` and
`∫_a^b f = lim_{n → ∞} ∫_{aₙ}^{bₙ} f`. -/
lemma riemannIntegral_tendsto_of_nested_intervals
    {a b : ℝ} {f : ℝ → ℝ} (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    {a_seq b_seq : ℕ → ℝ}
    (h_between : ∀ n, a < a_seq n ∧ a_seq n < b_seq n ∧ b_seq n < b)
    (ha : Tendsto a_seq atTop (𝓝 a)) (hb : Tendsto b_seq atTop (𝓝 b))
    (hf_seq : ∀ n, RiemannIntegrableOn f (a_seq n) (b_seq n)) :
    ∃ hf_ab : RiemannIntegrableOn f a b,
      Tendsto (fun n => riemannIntegral f (a_seq n) (b_seq n) (hf_seq n))
        atTop (𝓝 (riemannIntegral f a b hf_ab)) := by
  classical
  obtain ⟨M, hM⟩ := hbound
  have hab : a < b := by
    have h0 := h_between 0
    exact lt_trans h0.1 (lt_trans h0.2.1 h0.2.2)
  have hab_le : a ≤ b := le_of_lt hab
  have hM_nonneg : 0 ≤ M := by
    have h := hM a ⟨le_rfl, hab_le⟩
    exact le_trans (abs_nonneg _) h
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ f x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, f x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  let I : ℕ → ℝ := fun n => riemannIntegral f (a_seq n) (b_seq n) (hf_seq n)
  have hI_bdd : BoundedSequence I := by
    refine ⟨M * (b - a), ?_⟩
    intro n
    have hbn := h_between n
    have ha_le : a ≤ a_seq n := le_of_lt hbn.1
    have hb_le : b_seq n ≤ b := le_of_lt hbn.2.2
    have habn : a_seq n ≤ b_seq n := le_of_lt hbn.2.1
    have hmin_n : ∀ x ∈ Set.Icc (a_seq n) (b_seq n), -M ≤ f x := by
      intro x hx
      exact hmin x ⟨le_trans ha_le hx.1, le_trans hx.2 hb_le⟩
    have hmax_n : ∀ x ∈ Set.Icc (a_seq n) (b_seq n), f x ≤ M := by
      intro x hx
      exact hmax x ⟨le_trans ha_le hx.1, le_trans hx.2 hb_le⟩
    have hbounds :=
      riemannIntegral_bounds (f := f) (a := a_seq n) (b := b_seq n) (m := -M) (M := M)
        habn (hf_seq n) hmin_n hmax_n
    have hlen : b_seq n - a_seq n ≤ b - a := sub_le_sub hb_le ha_le
    have hupper : I n ≤ M * (b - a) := by
      have hupper' : I n ≤ M * (b_seq n - a_seq n) := hbounds.2
      have hlen' : M * (b_seq n - a_seq n) ≤ M * (b - a) :=
        mul_le_mul_of_nonneg_left hlen hM_nonneg
      exact le_trans hupper' hlen'
    have hlower : -M * (b - a) ≤ I n := by
      have hnonpos : (-M) ≤ 0 := by linarith [hM_nonneg]
      have hlen' : (-M) * (b - a) ≤ (-M) * (b_seq n - a_seq n) :=
        mul_le_mul_of_nonpos_left hlen hnonpos
      have hlower' : (-M) * (b_seq n - a_seq n) ≤ I n := by
        simpa using hbounds.1
      exact le_trans hlen' hlower'
    have hlower' : -(M * (b - a)) ≤ I n := by
      simpa [neg_mul] using hlower
    exact abs_le.mpr ⟨hlower', hupper⟩
  have h_lower_est :
      ∀ n,
        (-M) * (a_seq n - a) + I n - M * (b - b_seq n) ≤
          lowerDarbouxIntegral f a b := by
    intro n
    have hbn := h_between n
    have ha_lt : a < a_seq n := hbn.1
    have hab_lt : a_seq n < b_seq n := hbn.2.1
    have hb_lt : b_seq n < b := hbn.2.2
    have ha_lt_bseq : a < b_seq n := lt_trans ha_lt hab_lt
    have ha_le : a ≤ a_seq n := le_of_lt ha_lt
    have hb_le : b_seq n ≤ b := le_of_lt hb_lt
    have hmin_left : ∀ x ∈ Set.Icc a (a_seq n), -M ≤ f x := by
      intro x hx
      exact hmin x ⟨hx.1, le_trans hx.2 (le_of_lt (lt_trans hab_lt hb_lt))⟩
    have hmax_left : ∀ x ∈ Set.Icc a (a_seq n), f x ≤ M := by
      intro x hx
      exact hmax x ⟨hx.1, le_trans hx.2 (le_of_lt (lt_trans hab_lt hb_lt))⟩
    have hmin_right : ∀ x ∈ Set.Icc (b_seq n) b, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨le_trans (le_of_lt ha_lt_bseq) hx.1, hx.2⟩
    have hmax_right : ∀ x ∈ Set.Icc (b_seq n) b, f x ≤ M := by
      intro x hx
      exact hmax x ⟨le_trans (le_of_lt ha_lt_bseq) hx.1, hx.2⟩
    have hbound_abn : ∃ M : ℝ, ∀ x ∈ Set.Icc a (b_seq n), |f x| ≤ M := by
      refine ⟨M, ?_⟩
      intro x hx
      exact hM x ⟨hx.1, le_trans hx.2 hb_le⟩
    have hsplit_abn :=
      darbouxIntegral_add (a := a) (b := a_seq n) (c := b_seq n) (f := f)
        ha_lt hab_lt hbound_abn
    have hsplit_ab :=
      darbouxIntegral_add (a := a) (b := b_seq n) (c := b) (f := f)
        ha_lt_bseq hb_lt ⟨M, hM⟩
    have hsplit_lower :
        lowerDarbouxIntegral f a b =
          lowerDarbouxIntegral f a (a_seq n) +
            lowerDarbouxIntegral f (a_seq n) (b_seq n) +
              lowerDarbouxIntegral f (b_seq n) b := by
      calc
        lowerDarbouxIntegral f a b
            = lowerDarbouxIntegral f a (b_seq n) + lowerDarbouxIntegral f (b_seq n) b :=
              hsplit_ab.1
        _ =
            lowerDarbouxIntegral f a (a_seq n) +
              lowerDarbouxIntegral f (a_seq n) (b_seq n) +
                lowerDarbouxIntegral f (b_seq n) b := by
              simp [hsplit_abn.1, add_assoc]
    have hbound_left :=
      lower_upper_integral_bounds (f := f) (a := a) (b := a_seq n) (m := -M) (M := M)
        (le_of_lt ha_lt) hmin_left hmax_left
    have hbound_right :=
      lower_upper_integral_bounds (f := f) (a := b_seq n) (b := b) (m := -M) (M := M)
        (le_of_lt hb_lt) hmin_right hmax_right
    have h_lower_left : (-M) * (a_seq n - a) ≤ lowerDarbouxIntegral f a (a_seq n) :=
      hbound_left.1
    have h_lower_right : (-M) * (b - b_seq n) ≤ lowerDarbouxIntegral f (b_seq n) b :=
      hbound_right.1
    have hsum_le' :
        (-M) * (a_seq n - a) + lowerDarbouxIntegral f (a_seq n) (b_seq n) - M * (b - b_seq n) ≤
          lowerDarbouxIntegral f a (a_seq n) + lowerDarbouxIntegral f (a_seq n) (b_seq n) +
            lowerDarbouxIntegral f (b_seq n) b := by
      linarith [h_lower_left, h_lower_right]
    have hI_eq : I n = lowerDarbouxIntegral f (a_seq n) (b_seq n) := by
      simp [I, riemannIntegral]
    have hsum_le :
        (-M) * (a_seq n - a) + I n - M * (b - b_seq n) ≤
          lowerDarbouxIntegral f a (a_seq n) + lowerDarbouxIntegral f (a_seq n) (b_seq n) +
            lowerDarbouxIntegral f (b_seq n) b := by
      simpa [hI_eq] using hsum_le'
    have : (-M) * (a_seq n - a) + I n - M * (b - b_seq n) ≤
        lowerDarbouxIntegral f a b := by
      simpa [hsplit_lower] using hsum_le
    exact this
  have h_upper_est :
      ∀ n,
        upperDarbouxIntegral f a b ≤
          M * (a_seq n - a) + I n + M * (b - b_seq n) := by
    intro n
    have hbn := h_between n
    have ha_lt : a < a_seq n := hbn.1
    have hab_lt : a_seq n < b_seq n := hbn.2.1
    have hb_lt : b_seq n < b := hbn.2.2
    have ha_lt_bseq : a < b_seq n := lt_trans ha_lt hab_lt
    have hb_le : b_seq n ≤ b := le_of_lt hb_lt
    have hmin_left : ∀ x ∈ Set.Icc a (a_seq n), -M ≤ f x := by
      intro x hx
      exact hmin x ⟨hx.1, le_trans hx.2 (le_of_lt (lt_trans hab_lt hb_lt))⟩
    have hmax_left : ∀ x ∈ Set.Icc a (a_seq n), f x ≤ M := by
      intro x hx
      exact hmax x ⟨hx.1, le_trans hx.2 (le_of_lt (lt_trans hab_lt hb_lt))⟩
    have hmin_right : ∀ x ∈ Set.Icc (b_seq n) b, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨le_trans (le_of_lt ha_lt_bseq) hx.1, hx.2⟩
    have hmax_right : ∀ x ∈ Set.Icc (b_seq n) b, f x ≤ M := by
      intro x hx
      exact hmax x ⟨le_trans (le_of_lt ha_lt_bseq) hx.1, hx.2⟩
    have hbound_abn : ∃ M : ℝ, ∀ x ∈ Set.Icc a (b_seq n), |f x| ≤ M := by
      refine ⟨M, ?_⟩
      intro x hx
      exact hM x ⟨hx.1, le_trans hx.2 hb_le⟩
    have hsplit_abn :=
      darbouxIntegral_add (a := a) (b := a_seq n) (c := b_seq n) (f := f)
        ha_lt hab_lt hbound_abn
    have hsplit_ab :=
      darbouxIntegral_add (a := a) (b := b_seq n) (c := b) (f := f)
        ha_lt_bseq hb_lt ⟨M, hM⟩
    have hsplit_upper :
        upperDarbouxIntegral f a b =
          upperDarbouxIntegral f a (a_seq n) +
            upperDarbouxIntegral f (a_seq n) (b_seq n) +
              upperDarbouxIntegral f (b_seq n) b := by
      calc
        upperDarbouxIntegral f a b
            = upperDarbouxIntegral f a (b_seq n) + upperDarbouxIntegral f (b_seq n) b :=
              hsplit_ab.2
        _ =
            upperDarbouxIntegral f a (a_seq n) +
              upperDarbouxIntegral f (a_seq n) (b_seq n) +
                upperDarbouxIntegral f (b_seq n) b := by
              simp [hsplit_abn.2, add_assoc]
    have hbound_left :=
      lower_upper_integral_bounds (f := f) (a := a) (b := a_seq n) (m := -M) (M := M)
        (le_of_lt ha_lt) hmin_left hmax_left
    have hbound_right :=
      lower_upper_integral_bounds (f := f) (a := b_seq n) (b := b) (m := -M) (M := M)
        (le_of_lt hb_lt) hmin_right hmax_right
    have h_upper_left : upperDarbouxIntegral f a (a_seq n) ≤ M * (a_seq n - a) :=
      hbound_left.2.2
    have h_upper_right : upperDarbouxIntegral f (b_seq n) b ≤ M * (b - b_seq n) :=
      hbound_right.2.2
    have h_mid : upperDarbouxIntegral f (a_seq n) (b_seq n) = I n := by
      calc
        upperDarbouxIntegral f (a_seq n) (b_seq n) =
            lowerDarbouxIntegral f (a_seq n) (b_seq n) := (hf_seq n).2.symm
        _ = I n := by simp [I, riemannIntegral]
    have hsum_le' :
        upperDarbouxIntegral f a (a_seq n) + upperDarbouxIntegral f (a_seq n) (b_seq n) +
          upperDarbouxIntegral f (b_seq n) b ≤
            M * (a_seq n - a) + upperDarbouxIntegral f (a_seq n) (b_seq n) +
              M * (b - b_seq n) := by
      linarith [h_upper_left, h_upper_right]
    have hsum_le :
        upperDarbouxIntegral f a (a_seq n) + upperDarbouxIntegral f (a_seq n) (b_seq n) +
          upperDarbouxIntegral f (b_seq n) b ≤
            M * (a_seq n - a) + I n + M * (b - b_seq n) := by
      simpa [h_mid] using hsum_le'
    have : upperDarbouxIntegral f a b ≤ M * (a_seq n - a) + I n + M * (b - b_seq n) := by
      simpa [hsplit_upper] using hsum_le
    exact this
  have hsubseq_bounds :
      ∀ {s : RealSubsequence I} {L : ℝ},
        ConvergesTo (s.asSequence) L →
          L ≤ lowerDarbouxIntegral f a b ∧ upperDarbouxIntegral f a b ≤ L := by
    intro s L hconv
    let s_a : RealSubsequence a_seq := ⟨s.indices, s.strictlyIncreasing⟩
    let s_b : RealSubsequence b_seq := ⟨s.indices, s.strictlyIncreasing⟩
    have ha' : ConvergesTo a_seq a :=
      (convergesTo_iff_tendsto a_seq a).2 ha
    have hb' : ConvergesTo b_seq b :=
      (convergesTo_iff_tendsto b_seq b).2 hb
    have ha_sub : ConvergesTo (s_a.asSequence) a :=
      convergesTo_subsequence (x := a_seq) (l := a) ha' s_a
    have hb_sub : ConvergesTo (s_b.asSequence) b :=
      convergesTo_subsequence (x := b_seq) (l := b) hb' s_b
    have hconst_a : ConvergesTo (fun _ : ℕ => a) a := constant_seq_converges a
    have hconst_b : ConvergesTo (fun _ : ℕ => b) b := constant_seq_converges b
    have ha_diff : ConvergesTo (fun k => s_a.asSequence k - a) 0 := by
      simpa using (limit_sub_of_convergent ha_sub hconst_a)
    have hb_diff : ConvergesTo (fun k => b - s_b.asSequence k) 0 := by
      simpa using (limit_sub_of_convergent hconst_b hb_sub)
    have hconst_negM : ConvergesTo (fun _ : ℕ => -M) (-M) := constant_seq_converges (-M)
    have hconst_M : ConvergesTo (fun _ : ℕ => M) M := constant_seq_converges M
    have ha_mul_neg :
        ConvergesTo (fun k => (-M) * (s_a.asSequence k - a)) 0 := by
      simpa using (limit_mul_of_convergent hconst_negM ha_diff)
    have ha_mul_pos :
        ConvergesTo (fun k => M * (s_a.asSequence k - a)) 0 := by
      simpa using (limit_mul_of_convergent hconst_M ha_diff)
    have hb_mul_pos :
        ConvergesTo (fun k => M * (b - s_b.asSequence k)) 0 := by
      simpa using (limit_mul_of_convergent hconst_M hb_diff)
    have hI_sub : ConvergesTo (fun k => I (s.indices k)) L := by
      simpa [RealSubsequence.asSequence] using hconv
    have hA_add :
        ConvergesTo (fun k => (-M) * (a_seq (s.indices k) - a) + I (s.indices k)) L := by
      have h :=
        limit_add_of_convergent
          (by simpa [RealSubsequence.asSequence, s_a] using ha_mul_neg)
          hI_sub
      simpa using h
    have hA :
        ConvergesTo
          (fun k =>
            (-M) * (a_seq (s.indices k) - a) +
              I (s.indices k) -
              M * (b - b_seq (s.indices k))) L := by
      have h :=
        limit_sub_of_convergent hA_add
          (by simpa [RealSubsequence.asSequence, s_b] using hb_mul_pos)
      simpa [sub_eq_add_neg, add_assoc] using h
    have hB_add :
        ConvergesTo (fun k => M * (a_seq (s.indices k) - a) + I (s.indices k)) L := by
      have h :=
        limit_add_of_convergent
          (by simpa [RealSubsequence.asSequence, s_a] using ha_mul_pos)
          hI_sub
      simpa using h
    have hB :
        ConvergesTo
          (fun k =>
            M * (a_seq (s.indices k) - a) + I (s.indices k) + M * (b - b_seq (s.indices k))) L := by
      have h :=
        limit_add_of_convergent hB_add
          (by simpa [RealSubsequence.asSequence, s_b] using hb_mul_pos)
      simpa [add_assoc] using h
    have hA_le : ∀ k,
        (-M) * (a_seq (s.indices k) - a) + I (s.indices k) - M * (b - b_seq (s.indices k)) ≤
          lowerDarbouxIntegral f a b := by
      intro k
      simpa using h_lower_est (s.indices k)
    have hB_ge : ∀ k,
        upperDarbouxIntegral f a b ≤
          M * (a_seq (s.indices k) - a) + I (s.indices k) + M * (b - b_seq (s.indices k)) := by
      intro k
      simpa using h_upper_est (s.indices k)
    have hconst_lower :
        ConvergesTo (fun _ : ℕ => lowerDarbouxIntegral f a b)
          (lowerDarbouxIntegral f a b) := constant_seq_converges _
    have hconst_upper :
        ConvergesTo (fun _ : ℕ => upperDarbouxIntegral f a b)
          (upperDarbouxIntegral f a b) := constant_seq_converges _
    have hL_le :
        L ≤ lowerDarbouxIntegral f a b :=
      limit_le_of_pointwise_le hA hconst_lower hA_le
    have hupper_le :
        upperDarbouxIntegral f a b ≤ L :=
      limit_le_of_pointwise_le hconst_upper hB hB_ge
    exact ⟨hL_le, hupper_le⟩
  rcases bolzanoWeierstrass_real_sequence (x := I) hI_bdd with ⟨s, hsconv⟩
  rcases hsconv with ⟨L, hconv⟩
  have hbounds := hsubseq_bounds (s := s) (L := L) hconv
  have hle_lower : L ≤ lowerDarbouxIntegral f a b := hbounds.1
  have hupper_le_L : upperDarbouxIntegral f a b ≤ L := hbounds.2
  have hEq : lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
    have hbounds_ab :=
      lower_upper_integral_bounds (f := f) (a := a) (b := b) (m := -M) (M := M)
        hab_le hmin hmax
    have hle : lowerDarbouxIntegral f a b ≤ upperDarbouxIntegral f a b := hbounds_ab.2.1
    have hge : upperDarbouxIntegral f a b ≤ lowerDarbouxIntegral f a b :=
      le_trans hupper_le_L hle_lower
    exact le_antisymm hle hge
  have hf_ab : RiemannIntegrableOn f a b := ⟨⟨M, hM⟩, hEq⟩
  have hconv_I :
      ConvergesTo I (riemannIntegral f a b hf_ab) := by
    have hsub :
        ∀ s : RealSubsequence I,
          ConvergentSequence (s.asSequence) →
            ConvergesTo (s.asSequence) (riemannIntegral f a b hf_ab) := by
      intro s hsconv'
      rcases hsconv' with ⟨L', hconv'⟩
      have hbounds' := hsubseq_bounds (s := s) (L := L') hconv'
      have hle_lower' : L' ≤ lowerDarbouxIntegral f a b := hbounds'.1
      have hupper_le' : upperDarbouxIntegral f a b ≤ L' := hbounds'.2
      have hlower_le' : lowerDarbouxIntegral f a b ≤ L' := by
        simpa [hEq] using hupper_le'
      have hlower_eq : lowerDarbouxIntegral f a b = L' :=
        le_antisymm hlower_le' hle_lower'
      have hEq' : L' = riemannIntegral f a b hf_ab := by
        have : riemannIntegral f a b hf_ab = L' := by
          simp [riemannIntegral, hlower_eq]
        exact this.symm
      simpa [hEq'] using hconv'
    exact (converges_iff_convergent_subsequences_converge
      (x := I) (l := riemannIntegral f a b hf_ab) hI_bdd).2 hsub
  refine ⟨hf_ab, ?_⟩
  have hTendsto :
      Tendsto I atTop (𝓝 (riemannIntegral f a b hf_ab)) :=
    (convergesTo_iff_tendsto I (riemannIntegral f a b hf_ab)).1 hconv_I
  simpa [I] using hTendsto

lemma continuousOn_Icc_of_continuousAt {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ∀ x ∈ Set.Icc a b, ContinuousAt f x) :
    ContinuousOn f (Set.Icc a b) := by
  intro x hx
  exact (hcont x hx).continuousWithinAt

lemma riemannIntegrableOn_of_continuousAt_Ioo {a b : ℝ} {f : ℝ → ℝ}
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hcont : ∀ x ∈ Set.Ioo a b, ContinuousAt f x) :
    RiemannIntegrableOn f a b := by
  classical
  by_cases hab : a ≤ b
  · by_cases hlt : a < b
    · let a_seq : ℕ → ℝ := fun n => a + (b - a) / (n + 3 : ℝ)
      let b_seq : ℕ → ℝ := fun n => b - (b - a) / (n + 3 : ℝ)
      have h_between :
          ∀ n, a < a_seq n ∧ a_seq n < b_seq n ∧ b_seq n < b := by
        intro n
        set d : ℝ := (b - a) / (n + 3 : ℝ)
        have hpos : 0 < d := by
          have hpos_num : 0 < b - a := sub_pos.mpr hlt
          have hpos_den : 0 < (n + 3 : ℝ) := by
            exact_mod_cast (Nat.succ_pos (n + 2))
          simpa [d] using (div_pos hpos_num hpos_den)
        have h2lt_nat : 2 < n + 3 := by
          have h0 : 0 < n + 1 := Nat.succ_pos n
          have h1 : 1 < n + 2 := Nat.succ_lt_succ h0
          exact Nat.succ_lt_succ h1
        have h2lt : (2 : ℝ) < (n + 3 : ℝ) := by
          exact_mod_cast h2lt_nat
        have hdiv : (2 : ℝ) / (n + 3 : ℝ) < 1 := by
          exact (div_lt_one (by exact_mod_cast (Nat.succ_pos (n + 2)))).2 h2lt
        have hmul :
            (2 : ℝ) / (n + 3 : ℝ) * (b - a) < 1 * (b - a) :=
          mul_lt_mul_of_pos_right hdiv (sub_pos.mpr hlt)
        have h2d : 2 * d < b - a := by
          have hrewrite :
              (2 : ℝ) / (n + 3 : ℝ) * (b - a) = 2 * d := by
            simp [d, div_eq_mul_inv, mul_comm, mul_left_comm]
          simpa [hrewrite] using hmul
        have ha_lt : a < a_seq n := by
          simpa [a_seq, d] using (lt_add_of_pos_right a hpos)
        have hb_lt : b_seq n < b := by
          simpa [b_seq, d] using (sub_lt_self b hpos)
        have hab_lt : a_seq n < b_seq n := by
          have : a + d < b - d := by linarith [h2d]
          simpa [a_seq, b_seq, d] using this
        exact ⟨ha_lt, hab_lt, hb_lt⟩
      have hdiv :
          Tendsto (fun n : ℕ => (b - a) / (n + 3 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
        (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 3)
      have ha : Tendsto a_seq atTop (𝓝 a) := by
        have hconst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
        have h := hconst.add hdiv
        simpa [a_seq] using h
      have hb : Tendsto b_seq atTop (𝓝 b) := by
        have hconst : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
        have hdiv' :
            Tendsto (fun n : ℕ => -((b - a) / (n + 3 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
          simpa using hdiv.neg
        have h := hconst.add hdiv'
        simpa [b_seq, sub_eq_add_neg] using h
      have hf_seq : ∀ n, RiemannIntegrableOn f (a_seq n) (b_seq n) := by
        intro n
        have hcont_n : ContinuousOn f (Set.Icc (a_seq n) (b_seq n)) := by
          refine continuousOn_Icc_of_continuousAt ?_
          intro x hx
          have hbn := h_between n
          have hxIoo : x ∈ Set.Ioo a b := by
            refine ⟨lt_of_lt_of_le hbn.1 hx.1, ?_⟩
            exact lt_of_le_of_lt hx.2 hbn.2.2
          exact hcont x hxIoo
        exact continuousOn_riemannIntegrableOn hcont_n
      obtain ⟨hf_ab, _⟩ :=
        riemannIntegral_tendsto_of_nested_intervals hbound h_between ha hb hf_seq
      exact hf_ab
    · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
      subst hEq
      rcases hbound with ⟨M, hM⟩
      have hmin : ∀ x ∈ Set.Icc a a, -M ≤ f x := by
        intro x hx
        exact (abs_le.mp (hM x hx)).1
      have hmax : ∀ x ∈ Set.Icc a a, f x ≤ M := by
        intro x hx
        exact (abs_le.mp (hM x hx)).2
      have hbounds :=
        lower_upper_integral_bounds (f := f) (a := a) (b := a) (m := -M) (M := M)
          (by rfl) hmin hmax
      have hle : lowerDarbouxIntegral f a a ≤ upperDarbouxIntegral f a a := hbounds.2.1
      have hge : upperDarbouxIntegral f a a ≤ lowerDarbouxIntegral f a a := by
        have hlow : 0 ≤ lowerDarbouxIntegral f a a := by simpa using hbounds.1
        have hupp : upperDarbouxIntegral f a a ≤ 0 := by simpa using hbounds.2.2
        linarith
      exact ⟨⟨M, hM⟩, le_antisymm hle hge⟩
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
    have hEq :
        lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
      simp [lowerDarbouxIntegral, upperDarbouxIntegral, hno_lower, hno_upper]
    exact ⟨hbound, hEq⟩

/-- Theorem 5.2.9: A bounded function on `[a, b]` with only finitely many
discontinuities belongs to `ℛ([a, b])`, i.e., it is Riemann integrable. -/
theorem riemannIntegrableOn_of_finite_discontinuities {a b : ℝ} {f : ℝ → ℝ}
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hfinite : ({x | x ∈ Set.Icc a b ∧ ¬ ContinuousAt f x}).Finite) :
    RiemannIntegrableOn f a b := by
  classical
  have hfinite_int :
      ({x | x ∈ Set.Ioo a b ∧ ¬ ContinuousAt f x}).Finite := by
    refine hfinite.subset ?_
    intro x hx
    exact ⟨⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩, hx.2⟩
  have aux :
      ∀ n : ℕ,
        ∀ {a b : ℝ} {f : ℝ → ℝ},
          (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) →
          (hfinite : ({x | x ∈ Set.Ioo a b ∧ ¬ ContinuousAt f x}).Finite) →
          hfinite.toFinset.card = n →
          RiemannIntegrableOn f a b := by
    intro n
    refine
      Nat.strong_induction_on
        (p := fun n =>
          ∀ {a b : ℝ} {f : ℝ → ℝ},
            (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) →
            (hfinite :
              ({x | x ∈ Set.Ioo a b ∧ ¬ ContinuousAt f x}).Finite) →
            hfinite.toFinset.card = n →
            RiemannIntegrableOn f a b)
        n ?_
    intro n ih a b f hbound hfinite hcard
    cases n with
    | zero =>
        have hempty : hfinite.toFinset = ∅ := Finset.card_eq_zero.mp hcard
        have hcont : ∀ x ∈ Set.Ioo a b, ContinuousAt f x := by
          intro x hx
          by_contra hnot
          have hx' : x ∈ hfinite.toFinset := (hfinite.mem_toFinset).2 ⟨hx, hnot⟩
          rw [hempty] at hx'
          simpa using hx'
        exact riemannIntegrableOn_of_continuousAt_Ioo hbound hcont
    | succ n =>
        let D : Finset ℝ := hfinite.toFinset
        have hDcard : D.card = n + 1 := by
          simpa [D] using hcard
        have hD_nonempty : D.Nonempty := by
          apply Finset.card_pos.mp
          omega
        set c : ℝ := D.min' hD_nonempty with hc_def
        have hc_mem : c ∈ D := by
          simpa [c] using (Finset.min'_mem D hD_nonempty)
        have hcD : c ∈ Set.Ioo a b ∧ ¬ ContinuousAt f c := by
          have : c ∈ hfinite.toFinset := by simpa [D] using hc_mem
          exact (hfinite.mem_toFinset).1 this
        have hac : a < c := hcD.1.1
        have hcb : c < b := hcD.1.2
        have hmin : ∀ x ∈ D, c ≤ x := by
          have hmin' : c ∈ D ∧ ∀ x ∈ D, c ≤ x := by
            simpa [c] using
              (Finset.min'_eq_iff (s := D) (H := hD_nonempty) (a := c)).1 rfl
          exact hmin'.2
        have hcont_left : ∀ x ∈ Set.Ioo a c, ContinuousAt f x := by
          intro x hx
          by_contra hnot
          have hxIoo : x ∈ Set.Ioo a b := by
            exact ⟨hx.1, lt_trans hx.2 hcb⟩
          have hxD : x ∈ D := by
            have hxset : x ∈ {x | x ∈ Set.Ioo a b ∧ ¬ ContinuousAt f x} :=
              ⟨hxIoo, hnot⟩
            have : x ∈ hfinite.toFinset := (hfinite.mem_toFinset).2 hxset
            simpa [D] using this
          have hxle : c ≤ x := hmin x hxD
          exact (not_lt_of_ge hxle hx.2)
        rcases hbound with ⟨M, hM⟩
        have hbound_left : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M := by
          refine ⟨M, ?_⟩
          intro x hx
          exact hM x ⟨hx.1, le_trans hx.2 (le_of_lt hcb)⟩
        have hf_ac : RiemannIntegrableOn f a c :=
          riemannIntegrableOn_of_continuousAt_Ioo hbound_left hcont_left
        have hbound_right : ∃ M : ℝ, ∀ x ∈ Set.Icc c b, |f x| ≤ M := by
          refine ⟨M, ?_⟩
          intro x hx
          exact hM x ⟨le_trans (le_of_lt hac) hx.1, hx.2⟩
        have hfinite_right :
            ({x | x ∈ Set.Ioo c b ∧ ¬ ContinuousAt f x}).Finite := by
          refine hfinite.subset ?_
          intro x hx
          exact ⟨⟨lt_trans hac hx.1.1, hx.1.2⟩, hx.2⟩
        have hsubset : hfinite_right.toFinset ⊆ D := by
          intro x hx
          have hxset :
              x ∈ {x | x ∈ Set.Ioo c b ∧ ¬ ContinuousAt f x} :=
            (hfinite_right.mem_toFinset).1 hx
          have hxab : x ∈ Set.Ioo a b := ⟨lt_trans hac hxset.1.1, hxset.1.2⟩
          have hxset' :
              x ∈ {x | x ∈ Set.Ioo a b ∧ ¬ ContinuousAt f x} :=
            ⟨hxab, hxset.2⟩
          have : x ∈ hfinite.toFinset := (hfinite.mem_toFinset).2 hxset'
          simpa [D] using this
        have hc_not_right : c ∉ hfinite_right.toFinset := by
          intro hc'
          have hcset :
              c ∈ {x | x ∈ Set.Ioo c b ∧ ¬ ContinuousAt f x} :=
            (hfinite_right.mem_toFinset).1 hc'
          exact (lt_irrefl _ hcset.1.1)
        have hsubset' : hfinite_right.toFinset ⊂ D := by
          refine Finset.ssubset_iff_subset_ne.2 ?_
          refine ⟨hsubset, ?_⟩
          intro hEq
          have : c ∈ hfinite_right.toFinset := by
            rw [hEq]
            exact hc_mem
          exact hc_not_right this
        have hcard_lt : hfinite_right.toFinset.card < D.card :=
          Finset.card_lt_card hsubset'
        have hf_cb : RiemannIntegrableOn f c b :=
          ih (m := hfinite_right.toFinset.card)
            (by
              calc
                hfinite_right.toFinset.card < D.card := hcard_lt
                _ = n + 1 := hDcard)
            (a := c) (b := b) (f := f) hbound_right hfinite_right rfl
        exact (riemannIntegrableOn_interval_split hac hcb).2 ⟨hf_ac, hf_cb⟩
  exact aux (hfinite_int.toFinset.card) (a := a) (b := b) (f := f) hbound hfinite_int rfl

/-- If two functions agree on `Set.Icc a b`, they are simultaneously
Riemann integrable and have the same integral. -/
lemma riemannIntegral_congr_on_Icc {a b : ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc a b, g x = f x)
    (hf : RiemannIntegrableOn f a b) :
    ∃ hg : RiemannIntegrableOn g a b,
      riemannIntegral g a b hg = riemannIntegral f a b hf := by
  classical
  rcases hf with ⟨hbound_f, hEq_f⟩
  rcases hbound_f with ⟨M, hM⟩
  have hbound_g : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ M := by
    refine ⟨M, ?_⟩
    intro x hx
    simpa [hfg x hx] using hM x hx
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
  have lower_sum_congr :
      ∀ P : IntervalPartition a b, lowerDarbouxSum g P = lowerDarbouxSum f P := by
    intro P
    have lowerTag_congr (i : Fin P.n) : lowerTag g P i = lowerTag f P i := by
      have himage :
          g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
            f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ Set.Icc a b := subinterval_subset P i hx
          refine ⟨x, hx, ?_⟩
          symm
          exact hfg x hx'
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ Set.Icc a b := subinterval_subset P i hx
          refine ⟨x, hx, ?_⟩
          exact hfg x hx'
      simp [lowerTag, himage]
    classical
    calc
      lowerDarbouxSum g P =
          ∑ i : Fin P.n, lowerTag g P i * P.delta i := rfl
      _ = ∑ i : Fin P.n, lowerTag f P i * P.delta i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [lowerTag_congr]
      _ = lowerDarbouxSum f P := rfl
  have upper_sum_congr :
      ∀ P : IntervalPartition a b, upperDarbouxSum g P = upperDarbouxSum f P := by
    intro P
    have upperTag_congr (i : Fin P.n) : upperTag g P i = upperTag f P i := by
      have himage :
          g '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) =
            f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ Set.Icc a b := subinterval_subset P i hx
          refine ⟨x, hx, ?_⟩
          symm
          exact hfg x hx'
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ Set.Icc a b := subinterval_subset P i hx
          refine ⟨x, hx, ?_⟩
          exact hfg x hx'
      simp [upperTag, himage]
    classical
    calc
      upperDarbouxSum g P =
          ∑ i : Fin P.n, upperTag g P i * P.delta i := rfl
      _ = ∑ i : Fin P.n, upperTag f P i * P.delta i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [upperTag_congr]
      _ = upperDarbouxSum f P := rfl
  have hset_lower :
      Set.range (fun P : IntervalPartition a b => lowerDarbouxSum g P) =
        Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P) := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P, by simp [lower_sum_congr P]⟩
    · rintro ⟨P, rfl⟩
      exact ⟨P, by simp [lower_sum_congr P]⟩
  have hset_upper :
      Set.range (fun P : IntervalPartition a b => upperDarbouxSum g P) =
        Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P) := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P, by simp [upper_sum_congr P]⟩
    · rintro ⟨P, rfl⟩
      exact ⟨P, by simp [upper_sum_congr P]⟩
  have hEq_lower :
      lowerDarbouxIntegral g a b = lowerDarbouxIntegral f a b := by
    simp [lowerDarbouxIntegral, hset_lower]
  have hEq_upper :
      upperDarbouxIntegral g a b = upperDarbouxIntegral f a b := by
    simp [upperDarbouxIntegral, hset_upper]
  have hEq_g :
      lowerDarbouxIntegral g a b = upperDarbouxIntegral g a b := by
    calc
      lowerDarbouxIntegral g a b = lowerDarbouxIntegral f a b := hEq_lower
      _ = upperDarbouxIntegral f a b := hEq_f
      _ = upperDarbouxIntegral g a b := hEq_upper.symm
  refine ⟨⟨hbound_g, hEq_g⟩, ?_⟩
  simp [riemannIntegral, hEq_lower]

end Section02
end Chap05
