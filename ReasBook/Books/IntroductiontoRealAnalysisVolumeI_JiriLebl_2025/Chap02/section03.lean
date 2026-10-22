/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section02

section Chap02
section Section03

/-- The upper tail supremum sequence `a_n = sup { x_k | k ≥ n }` attached to a
real sequence `x`. -/
noncomputable def tailSupSequence (x : RealSequence) (n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ k ≥ n, y = x k}

/-- The lower tail infimum sequence `b_n = inf { x_k | k ≥ n }` attached to a
real sequence `x`. -/
noncomputable def tailInfSequence (x : RealSequence) (n : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ k ≥ n, y = x k}

/-- The limit superior of a real sequence, realized as the infimum of the tail
suprema. -/
noncomputable def limsupSequence (x : RealSequence) : ℝ :=
  sInf (Set.range (tailSupSequence x))

/-- The limit inferior of a real sequence, realized as the supremum of the tail
infima. -/
noncomputable def liminfSequence (x : RealSequence) : ℝ :=
  sSup (Set.range (tailInfSequence x))

/-- Proposition 2.3.2: For a bounded sequence `{x_n}`, with `a_n` the tail
suprema and `b_n` the tail infima as above: (i) `{a_n}` is bounded and
monotone decreasing while `{b_n}` is bounded and monotone increasing, so
`liminf_{n → ∞} x_n` and `limsup_{n → ∞} x_n` exist; (ii)
`limsup_{n → ∞} x_n = inf { a_n : n ∈ ℕ }` and
`liminf_{n → ∞} x_n = sup { b_n : n ∈ ℕ }`; (iii)
`liminf_{n → ∞} x_n ≤ limsup_{n → ∞} x_n`. -/
theorem limsup_liminf_properties (x : RealSequence) (hx : BoundedSequence x) :
    MonotoneDecreasingSequence (tailSupSequence x) ∧
      MonotoneIncreasingSequence (tailInfSequence x) ∧
        ConvergentSequence (tailSupSequence x) ∧
          ConvergentSequence (tailInfSequence x) ∧
            limsupSequence x = sInf (Set.range (tailSupSequence x)) ∧
              liminfSequence x = sSup (Set.range (tailInfSequence x)) ∧
                liminfSequence x ≤ limsupSequence x := by
  classical
  obtain ⟨B, hB⟩ := hx
  have h_upper : ∀ n, x n ≤ B := fun n => (abs_le.mp (hB n)).2
  have h_lower : ∀ n, -B ≤ x n := fun n => (abs_le.mp (hB n)).1
  let A : ℕ → Set ℝ := fun n => {y : ℝ | ∃ k ≥ n, y = x k}
  have hNonempty : ∀ n, (A n).Nonempty := fun n => ⟨x n, ⟨n, le_rfl, rfl⟩⟩
  have hBddAbove : ∀ n, BddAbove (A n) := by
    intro n
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact h_upper k
  have hBddBelow : ∀ n, BddBelow (A n) := by
    intro n
    refine ⟨-B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact h_lower k
  -- Monotonicity of the tail supremum sequence.
  have hmonoSup : MonotoneDecreasingSequence (tailSupSequence x) := by
    intro n
    have hsubset : A (n + 1) ⊆ A n := by
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact ⟨k, le_trans (Nat.le_succ n) hk, rfl⟩
    have h := csSup_le_csSup (hBddAbove n) (hNonempty (n + 1)) hsubset
    simpa [tailSupSequence, A, Nat.succ_eq_add_one] using h
  -- Monotonicity of the tail infimum sequence.
  have hmonoInf : MonotoneIncreasingSequence (tailInfSequence x) := by
    intro n
    have hsubset : A (n + 1) ⊆ A n := by
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact ⟨k, le_trans (Nat.le_succ n) hk, rfl⟩
    have h := csInf_le_csInf (hBddBelow n) (hNonempty (n + 1)) hsubset
    simpa [tailInfSequence, A, Nat.succ_eq_add_one] using h
  -- Boundedness of the tail supremum sequence.
  have hBoundSup : BoundedSequence (tailSupSequence x) := by
    refine ⟨B, ?_⟩
    intro n
    have hupper : tailSupSequence x n ≤ B := by
      dsimp [tailSupSequence, A]
      refine csSup_le (hNonempty n) ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact h_upper k
    have hlower : -B ≤ tailSupSequence x n := by
      have hmem : x n ∈ A n := ⟨n, le_rfl, rfl⟩
      have hxge : -B ≤ x n := h_lower n
      have hsup : x n ≤ tailSupSequence x n := by
        simpa [tailSupSequence, A] using (le_csSup (hBddAbove n) hmem)
      exact le_trans hxge hsup
    exact abs_le.mpr ⟨hlower, hupper⟩
  -- Boundedness of the tail infimum sequence.
  have hBoundInf : BoundedSequence (tailInfSequence x) := by
    refine ⟨B, ?_⟩
    intro n
    have hupper : tailInfSequence x n ≤ B := by
      have hmem : x n ∈ A n := ⟨n, le_rfl, rfl⟩
      have hinf_le : tailInfSequence x n ≤ x n := by
        simpa [tailInfSequence, A] using (csInf_le (hBddBelow n) hmem)
      exact le_trans hinf_le (h_upper n)
    have hlower : -B ≤ tailInfSequence x n := by
      dsimp [tailInfSequence, A]
      refine le_csInf (hNonempty n) ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact h_lower k
    exact abs_le.mpr ⟨hlower, hupper⟩
  -- Convergence of both tail sequences by the monotone convergence theorem.
  have hconvSup :
      ConvergesTo (tailSupSequence x) (sInf (Set.range (tailSupSequence x))) :=
    monotoneDecreasingSequence_tendsto_inf hmonoSup hBoundSup
  have hconvInf :
      ConvergesTo (tailInfSequence x) (sSup (Set.range (tailInfSequence x))) :=
    monotoneIncreasingSequence_tendsto_sup hmonoInf hBoundInf
  have hAntitoneSup : Antitone (tailSupSequence x) :=
    antitone_nat_of_succ_le (by
      intro n
      simpa [Nat.succ_eq_add_one] using hmonoSup n)
  have hMonotoneInf : Monotone (tailInfSequence x) :=
    monotone_nat_of_le_succ (by
      intro n
      simpa [Nat.succ_eq_add_one] using hmonoInf n)
  have hpointwise : ∀ n, tailInfSequence x n ≤ tailSupSequence x n := by
    intro n
    have hmem : x n ∈ A n := ⟨n, le_rfl, rfl⟩
    have hinf_le : tailInfSequence x n ≤ x n := by
      simpa [tailInfSequence, A] using (csInf_le (hBddBelow n) hmem)
    have hsup_ge : x n ≤ tailSupSequence x n := by
      simpa [tailSupSequence, A] using (le_csSup (hBddAbove n) hmem)
    exact le_trans hinf_le hsup_ge
  have hlim_le : liminfSequence x ≤ limsupSequence x := by
    have hUpper : ∀ m, liminfSequence x ≤ tailSupSequence x m := by
      intro m
      have hnonemptyRange :
          (Set.range (tailInfSequence x)).Nonempty :=
        ⟨tailInfSequence x 0, ⟨0, rfl⟩⟩
      refine csSup_le hnonemptyRange ?_
      intro y hy
      rcases hy with ⟨n, rfl⟩
      cases le_total m n with
      | inl hmn =>
          have hsup_mono : tailSupSequence x n ≤ tailSupSequence x m :=
            hAntitoneSup hmn
          exact le_trans (hpointwise n) hsup_mono
      | inr hnm =>
          have hInf_mono : tailInfSequence x n ≤ tailInfSequence x m :=
            hMonotoneInf hnm
          exact le_trans hInf_mono (hpointwise m)
    have hRangeSup : (Set.range (tailSupSequence x)).Nonempty :=
      ⟨tailSupSequence x 0, ⟨0, rfl⟩⟩
    have hle : ∀ y ∈ Set.range (tailSupSequence x), liminfSequence x ≤ y := by
      intro y hy
      rcases hy with ⟨m, rfl⟩
      exact hUpper m
    have h := le_csInf hRangeSup hle
    simpa [liminfSequence, limsupSequence] using h
  refine ⟨hmonoSup, hmonoInf, ⟨_, hconvSup⟩, ⟨_, hconvInf⟩, rfl, rfl, hlim_le⟩

/-- Definition 2.3.1: For a bounded real sequence `{x_n}`, define the tail
suprema `a_n = sup { x_k | k ≥ n }` and tail infima `b_n = inf { x_k | k ≥ n }`.
When the limits of these tails exist, set
`limsup_{n → ∞} x_n = lim_{n → ∞} a_n` and
`liminf_{n → ∞} x_n = lim_{n → ∞} b_n`. -/
lemma limsup_liminf_def_via_tail_extrema {x : RealSequence} (hx : BoundedSequence x)
    {L_sup L_inf : ℝ}
    (h_sup : ConvergesTo (tailSupSequence x) L_sup)
    (h_inf : ConvergesTo (tailInfSequence x) L_inf) :
    limsupSequence x = L_sup ∧ liminfSequence x = L_inf := by
  classical
  -- monotonicity and boundedness of the tail sequences
  rcases limsup_liminf_properties x hx with
    ⟨hmonoSup, hmonoInf, hconvSupExist, hconvInfExist, hlimsup_def, hliminf_def, _⟩
  have hBoundSup : BoundedSequence (tailSupSequence x) :=
    convergentSequence_bounded hconvSupExist
  have hBoundInf : BoundedSequence (tailInfSequence x) :=
    convergentSequence_bounded hconvInfExist
  -- canonical limits supplied by monotone convergence
  have hconvSup' :
      ConvergesTo (tailSupSequence x) (sInf (Set.range (tailSupSequence x))) :=
    monotoneDecreasingSequence_tendsto_inf hmonoSup hBoundSup
  have hconvInf' :
      ConvergesTo (tailInfSequence x) (sSup (Set.range (tailInfSequence x))) :=
    monotoneIncreasingSequence_tendsto_sup hmonoInf hBoundInf
  have hsup_eq : L_sup = sInf (Set.range (tailSupSequence x)) :=
    convergesTo_unique h_sup hconvSup'
  have hinf_eq : L_inf = sSup (Set.range (tailInfSequence x)) :=
    convergesTo_unique h_inf hconvInf'
  constructor
  · calc
      limsupSequence x = sInf (Set.range (tailSupSequence x)) := rfl
      _ = L_sup := by simp [hsup_eq]
  · calc
      liminfSequence x = sSup (Set.range (tailInfSequence x)) := rfl
      _ = L_inf := by simp [hinf_eq]

/-- Example 2.3.3: For the sequence defined by
`xₙ = (n + 1) / n` when `n` is odd and `xₙ = 0` when `n` is even, the limit
inferior is `0`, the limit superior is `1`, and the sequence does not
converge. -/
noncomputable def limsupLiminfExampleSequence : RealSequence :=
  fun n => if Odd n.succ then ((n.succ + 1 : ℝ) / n.succ) else 0

/-- The terms of the sequence in Example 2.3.3 are nonnegative and bounded by
`2`. -/
lemma limsupLiminfExampleSequence_bounds :
    ∀ n, 0 ≤ limsupLiminfExampleSequence n ∧
      limsupLiminfExampleSequence n ≤ 2 := by
  intro n
  by_cases hodd : Odd n.succ
  · have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hrepr :
        ((n.succ + 1 : ℝ) / n.succ) = 1 + (1 : ℝ) / n.succ := by
      have hne : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp [hne]
    have hfrac_le_one : (1 : ℝ) / n.succ ≤ 1 := by
      have hle : (1 : ℝ) ≤ (n.succ : ℝ) :=
        by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      have hpos' : 0 < (1 : ℝ) := by norm_num
      have h := one_div_le_one_div_of_le hpos' hle
      simpa using h
    have hnonneg :
        0 ≤ ((n.succ + 1 : ℝ) / n.succ) :=
      by
        have hpos' : 0 ≤ (n.succ : ℝ) := le_of_lt hpos
        exact div_nonneg (by linarith) hpos'
    have hle_two :
        ((n.succ + 1 : ℝ) / n.succ) ≤ 2 := by
      linarith [hrepr, hfrac_le_one]
    have hval :
        limsupLiminfExampleSequence n = ((n.succ + 1 : ℝ) / n.succ) := by
      simp [limsupLiminfExampleSequence, hodd]
    exact ⟨by simpa [hval] using hnonneg, by simpa [hval] using hle_two⟩
  · have hval : limsupLiminfExampleSequence n = 0 := by
      simp [limsupLiminfExampleSequence, hodd]
    exact ⟨by simp [hval], by simp [hval]⟩

/-- Every tail infimum of the sequence in Example 2.3.3 equals `0`. -/
lemma limsupLiminfExample_tailInf_zero (n : ℕ) :
    tailInfSequence limsupLiminfExampleSequence n = 0 := by
  classical
  let A : Set ℝ := {y : ℝ | ∃ k ≥ n, y = limsupLiminfExampleSequence k}
  have hnonempty : A.Nonempty :=
    ⟨limsupLiminfExampleSequence n, ⟨n, le_rfl, rfl⟩⟩
  have hLower : ∀ y ∈ A, 0 ≤ y := by
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact (limsupLiminfExampleSequence_bounds k).1
  have hge : 0 ≤ tailInfSequence limsupLiminfExampleSequence n := by
    refine le_csInf hnonempty ?_
    intro y hy
    exact hLower y hy
  have hzero_mem : 0 ∈ A := by
    refine ⟨2 * n + 1, ?_, ?_⟩
    · nlinarith
    · simp [limsupLiminfExampleSequence, Nat.succ_eq_add_one, Nat.odd_add]
  have hle : tailInfSequence limsupLiminfExampleSequence n ≤ 0 := by
    have hBddBelow : BddBelow A := ⟨0, hLower⟩
    simpa [tailInfSequence, A] using (csInf_le hBddBelow hzero_mem)
  exact le_antisymm hle hge

/-- The tail supremum of the sequence in Example 2.3.3 admits a closed
formula matching the textbook description. -/
lemma limsupLiminfExample_tailSup_formula (n : ℕ) :
    tailSupSequence limsupLiminfExampleSequence n =
      if Odd n.succ then ((n.succ + 1 : ℝ) / n.succ)
      else ((n.succ + 2 : ℝ) / (n.succ + 1)) := by
  classical
  let A : Set ℝ := {y : ℝ | ∃ k ≥ n, y = limsupLiminfExampleSequence k}
  have hnonempty : A.Nonempty :=
    ⟨limsupLiminfExampleSequence n, ⟨n, le_rfl, rfl⟩⟩
  have hBdd : BddAbove A := by
    refine ⟨2, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    linarith [(limsupLiminfExampleSequence_bounds k).2]
  by_cases hodd : Odd n.succ
  · -- `n` itself yields the tail supremum
    have hx_n :
        limsupLiminfExampleSequence n = ((n.succ + 1 : ℝ) / n.succ) := by
      simp [limsupLiminfExampleSequence, hodd]
    have hupper :
        ∀ y ∈ A, y ≤ limsupLiminfExampleSequence n := by
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      by_cases hkodd : Odd k.succ
      · have hle : (n.succ : ℝ) ≤ k.succ := by
          exact_mod_cast Nat.succ_le_succ hk
        have hdiv :
            (1 : ℝ) / k.succ ≤ (1 : ℝ) / n.succ :=
          one_div_le_one_div_of_le (by exact_mod_cast Nat.succ_pos n) hle
        have hxk :
            limsupLiminfExampleSequence k =
              ((k.succ + 1 : ℝ) / k.succ) := by
          simp [limsupLiminfExampleSequence, hkodd]
        have hrepr_k :
            ((k.succ + 1 : ℝ) / k.succ) = 1 + (1 : ℝ) / k.succ := by
          have hne : (k.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
          field_simp [hne]
        have hrepr_n :
            ((n.succ + 1 : ℝ) / n.succ) = 1 + (1 : ℝ) / n.succ := by
          have hne : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          field_simp [hne]
        have hfrac :
            ((k.succ + 1 : ℝ) / k.succ) ≤
              ((n.succ + 1 : ℝ) / n.succ) := by
          linarith
        simpa [hxk, hx_n] using hfrac
      · have hxk : limsupLiminfExampleSequence k = 0 := by
          simp [limsupLiminfExampleSequence, hkodd]
        have hnonneg : 0 ≤ limsupLiminfExampleSequence n :=
          (limsupLiminfExampleSequence_bounds n).1
        linarith
    have hsup_le :
        tailSupSequence limsupLiminfExampleSequence n ≤
          limsupLiminfExampleSequence n := by
      have h := csSup_le hnonempty hupper
      simpa [tailSupSequence, A] using h
    have hle_sup :
        limsupLiminfExampleSequence n ≤
          tailSupSequence limsupLiminfExampleSequence n := by
      have hmem : limsupLiminfExampleSequence n ∈ A := ⟨n, le_rfl, rfl⟩
      have h := le_csSup hBdd hmem
      simpa [tailSupSequence, A] using h
    have hEq :
        tailSupSequence limsupLiminfExampleSequence n =
          limsupLiminfExampleSequence n :=
      le_antisymm hsup_le hle_sup
    simpa [hodd, hx_n] using hEq
  · -- the first odd index in the tail is `n.succ`
    have hodd_succ : Odd n.succ.succ := (Nat.odd_add_one).2 hodd
    have hx_ns :
        limsupLiminfExampleSequence n.succ =
          ((n.succ + 2 : ℝ) / (n.succ + 1)) := by
      simp [limsupLiminfExampleSequence, hodd_succ, Nat.succ_eq_add_one]
      ring_nf
    have hupper :
        ∀ y ∈ A, y ≤ limsupLiminfExampleSequence n.succ := by
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      by_cases hkodd : Odd k.succ
      · have hkne : k ≠ n := by
          intro hk'
          subst hk'
          exact hodd hkodd
        have hk_ge : n.succ + 1 ≤ k.succ := by
          have hk' : n + 1 ≤ k :=
            Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk hkne.symm)
          exact Nat.succ_le_succ hk'
        have hdiv :
            (1 : ℝ) / k.succ ≤ (1 : ℝ) / (n.succ + 1) :=
          one_div_le_one_div_of_le (by nlinarith) (by exact_mod_cast hk_ge)
        have hxk :
            limsupLiminfExampleSequence k =
              ((k.succ + 1 : ℝ) / k.succ) := by
          simp [limsupLiminfExampleSequence, hkodd]
        have hrepr_k :
            ((k.succ + 1 : ℝ) / k.succ) = 1 + (1 : ℝ) / k.succ := by
          have hne : (k.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
          field_simp [hne]
        have hrepr_n :
            ((n.succ + 2 : ℝ) / (n.succ + 1)) =
              1 + (1 : ℝ) / (n.succ + 1) := by
          have hne : (n.succ + 1 : ℝ) ≠ 0 := by nlinarith
          field_simp [hne]
          ring_nf
        have hfrac :
            ((k.succ + 1 : ℝ) / k.succ) ≤
              ((n.succ + 2 : ℝ) / (n.succ + 1)) := by
          linarith
        simpa [hxk, hx_ns] using hfrac
      · have hxk : limsupLiminfExampleSequence k = 0 := by
          simp [limsupLiminfExampleSequence, hkodd]
        have hnonneg : 0 ≤ limsupLiminfExampleSequence n.succ :=
          (limsupLiminfExampleSequence_bounds n.succ).1
        linarith
    have hsup_le :
        tailSupSequence limsupLiminfExampleSequence n ≤
          limsupLiminfExampleSequence n.succ := by
      have h := csSup_le hnonempty hupper
      simpa [tailSupSequence, A] using h
    have hle_sup :
        limsupLiminfExampleSequence n.succ ≤
          tailSupSequence limsupLiminfExampleSequence n := by
      have hmem : limsupLiminfExampleSequence n.succ ∈ A :=
        ⟨n.succ, Nat.le_succ n, rfl⟩
      have h := le_csSup hBdd hmem
      simpa [tailSupSequence, A] using h
    have hEq :
        tailSupSequence limsupLiminfExampleSequence n =
          limsupLiminfExampleSequence n.succ :=
      le_antisymm hsup_le hle_sup
    have hEq' :
        tailSupSequence limsupLiminfExampleSequence n =
          ((n.succ + 2 : ℝ) / (n.succ + 1)) := by
      simpa [hx_ns] using hEq
    simpa [hodd, hx_ns] using hEq'

/-- The tail supremum sequence in Example 2.3.3 converges to `1`. -/
lemma limsupLiminfExample_tailSup_tendsto_one :
    ConvergesTo (tailSupSequence limsupLiminfExampleSequence) 1 := by
  classical
  let a : RealSequence :=
    fun n =>
      if Odd n.succ then (1 : ℝ) / n.succ else (1 : ℝ) / (n.succ + 1)
  have htail :
      ∀ n, tailSupSequence limsupLiminfExampleSequence n = 1 + a n := by
    intro n
    by_cases hodd : Odd n.succ
    · have hvalue :
        tailSupSequence limsupLiminfExampleSequence n =
          ((n.succ + 1 : ℝ) / n.succ) := by
        have h := limsupLiminfExample_tailSup_formula n
        simpa [hodd] using h
      have hrepr :
          ((n.succ + 1 : ℝ) / n.succ) = 1 + (1 : ℝ) / n.succ := by
        have hne : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        field_simp [hne]
      have ha : a n = (1 : ℝ) / n.succ := by
        simp [a, hodd]
      calc
        tailSupSequence limsupLiminfExampleSequence n =
            ((n.succ + 1 : ℝ) / n.succ) := hvalue
        _ = 1 + (1 : ℝ) / n.succ := hrepr
        _ = 1 + a n := by simp [ha]
    · have hvalue :
        tailSupSequence limsupLiminfExampleSequence n =
          ((n.succ + 2 : ℝ) / (n.succ + 1)) := by
        have h := limsupLiminfExample_tailSup_formula n
        simpa [hodd] using h
      have hrepr :
          ((n.succ + 2 : ℝ) / (n.succ + 1)) =
            1 + (1 : ℝ) / (n.succ + 1) := by
        have hne : (n.succ + 1 : ℝ) ≠ 0 :=
          by exact_mod_cast Nat.succ_ne_zero n.succ
        field_simp [hne]
        ring
      have ha : a n = (1 : ℝ) / (n.succ + 1) := by
        simp [a, hodd]
      calc
        tailSupSequence limsupLiminfExampleSequence n =
            ((n.succ + 2 : ℝ) / (n.succ + 1)) := hvalue
        _ = 1 + (1 : ℝ) / (n.succ + 1) := hrepr
        _ = 1 + a n := by simp [ha]
  have hnonneg : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    by_cases hodd : Odd n.succ
    · have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hpos' : 0 ≤ (n.succ : ℝ) := le_of_lt hpos
      have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hpos'
      simpa [hodd] using h
    · have hpos : 0 < (n.succ + 1 : ℝ) := by nlinarith
      have hpos' : 0 ≤ (n.succ + 1 : ℝ) := le_of_lt hpos
      have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hpos'
      simpa [hodd] using h
  have hle_one_div :
      ∀ n, a n ≤ (1 : ℝ) / n.succ := by
    intro n
    by_cases hodd : Odd n.succ
    · simp [a, hodd]
    · have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hle : (n.succ : ℝ) ≤ n.succ + 1 := by linarith
      have hdiv :
          (1 : ℝ) / (n.succ + 1) ≤ (1 : ℝ) / n.succ :=
        one_div_le_one_div_of_le hpos hle
      simpa [a, hodd] using hdiv
  have hconv_a_zero : ConvergesTo a 0 := by
    have hconst0 : ConvergesTo (fun _ : ℕ => (0 : ℝ)) 0 :=
      constant_seq_converges 0
    have hinv : ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0 :=
      inv_nat_converges_to_zero
    have hax : ∀ n, (fun _ : ℕ => (0 : ℝ)) n ≤ a n := by
      intro n
      have := hnonneg n
      linarith
    have hxb :
        ∀ n, a n ≤ (fun n : ℕ => (1 : ℝ) / (n + 1)) n := by
      intro n
      simpa using hle_one_div n
    exact squeeze_converges hax hxb hconst0 hinv
  have hconst1 : ConvergesTo (fun _ : ℕ => (1 : ℝ)) 1 :=
    constant_seq_converges 1
  have hsum : ConvergesTo (fun n => (1 : ℝ) + a n) (1 + 0) :=
    limit_add_of_convergent (x := fun _ => (1 : ℝ))
      (y := a) (l := 1) (m := 0) hconst1 hconv_a_zero
  have hsum' : ConvergesTo (fun n => 1 + a n) 1 := by
    simpa using hsum
  have htail_fun :
      tailSupSequence limsupLiminfExampleSequence = fun n => 1 + a n := by
    funext n
    exact htail n
  simpa [htail_fun] using hsum'

/-- Example 2.3.3, continued: the sequence above has `liminf = 0`, `limsup = 1`
and is divergent. -/
lemma limsupLiminfExample_values :
    liminfSequence limsupLiminfExampleSequence = 0 ∧
      limsupSequence limsupLiminfExampleSequence = 1 ∧
        ¬ ConvergentSequence limsupLiminfExampleSequence := by
  classical
  have hbounded : BoundedSequence limsupLiminfExampleSequence := by
    refine ⟨2, ?_⟩
    intro n
    have h := limsupLiminfExampleSequence_bounds n
    have hnonneg := h.1
    have hle := h.2
    have habs : |limsupLiminfExampleSequence n| =
        limsupLiminfExampleSequence n :=
      abs_of_nonneg hnonneg
    simpa [habs] using hle
  have hprops :=
    limsup_liminf_properties limsupLiminfExampleSequence hbounded
  rcases hprops with
    ⟨hmonoSup, _, ⟨_, hconvSup⟩, _, hlimsup_eq, _, _⟩
  -- bounds for the tail supremum sequence
  have hBoundSup : BoundedSequence (tailSupSequence limsupLiminfExampleSequence) := by
    refine ⟨2, ?_⟩
    intro n
    have hnonempty :
        ({y : ℝ | ∃ k ≥ n, y = limsupLiminfExampleSequence k}).Nonempty :=
      ⟨limsupLiminfExampleSequence n, ⟨n, le_rfl, rfl⟩⟩
    have hupper :
        tailSupSequence limsupLiminfExampleSequence n ≤ 2 := by
      dsimp [tailSupSequence]
      refine csSup_le hnonempty ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact (limsupLiminfExampleSequence_bounds k).2
    have hBdd :
        BddAbove {y : ℝ | ∃ k ≥ n, y = limsupLiminfExampleSequence k} := by
      refine ⟨2, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact (limsupLiminfExampleSequence_bounds k).2
    have hzero_mem :
        0 ∈ {y : ℝ | ∃ k ≥ n, y = limsupLiminfExampleSequence k} := by
      refine ⟨2 * n + 1, ?_, ?_⟩
      · nlinarith
      · simp [limsupLiminfExampleSequence, Nat.succ_eq_add_one, Nat.odd_add]
    have hnonneg : 0 ≤ tailSupSequence limsupLiminfExampleSequence n := by
      have h := le_csSup hBdd hzero_mem
      simpa [tailSupSequence] using h
    have habs : |tailSupSequence limsupLiminfExampleSequence n| =
        tailSupSequence limsupLiminfExampleSequence n :=
      abs_of_nonneg hnonneg
    simpa [habs] using hupper
  have hconvSup_inf :
      ConvergesTo (tailSupSequence limsupLiminfExampleSequence)
        (sInf (Set.range (tailSupSequence limsupLiminfExampleSequence))) :=
    monotoneDecreasingSequence_tendsto_inf hmonoSup hBoundSup
  -- compute liminf directly
  have hliminf :
      liminfSequence limsupLiminfExampleSequence = 0 := by
    have hrange :
        Set.range (tailInfSequence limsupLiminfExampleSequence) = {0} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨n, rfl⟩
        simp [limsupLiminfExample_tailInf_zero n]
      · intro hx
        rcases hx with rfl
        exact ⟨0, by simp [limsupLiminfExample_tailInf_zero]⟩
    simp [liminfSequence, hrange]
  -- compute limsup using convergence of the tail suprema
  have hsup_sInf :
      sInf (Set.range (tailSupSequence limsupLiminfExampleSequence)) = 1 :=
    convergesTo_unique hconvSup_inf limsupLiminfExample_tailSup_tendsto_one
  have hlimsup :
      limsupSequence limsupLiminfExampleSequence = 1 := by
    simpa [hlimsup_eq] using hsup_sInf
  -- divergence via two subsequences with distinct limits
  have hconst_odd :
      (fun i : ℕ => limsupLiminfExampleSequence (2 * i + 1)) =
        fun _ : ℕ => (0 : ℝ) := by
    funext i
    simp [limsupLiminfExampleSequence, Nat.succ_eq_add_one, Nat.odd_add]
  have hodd_const :
      ConvergesTo (fun i : ℕ => limsupLiminfExampleSequence (2 * i + 1)) 0 := by
    simpa [hconst_odd] using (constant_seq_converges (0 : ℝ))
  have hparity_even (i : ℕ) : Odd (Nat.succ (2 * i)) := by
    refine ⟨i, by simp [Nat.succ_eq_add_one]⟩
  have hconst_even :
      (fun i : ℕ => tailSupSequence limsupLiminfExampleSequence (2 * i)) =
        fun i : ℕ => limsupLiminfExampleSequence (2 * i) := by
    funext i
    have h := limsupLiminfExample_tailSup_formula (2 * i)
    have hodd : Odd (Nat.succ (2 * i)) := hparity_even i
    have hs : (2 * i).succ = 2 * i + 1 := by
      simp [Nat.succ_eq_add_one]
    simp [hodd] at h
    simpa [limsupLiminfExampleSequence, hodd, hs] using h
  have hsub_even_sup :
      ConvergesTo (fun i : ℕ =>
        tailSupSequence limsupLiminfExampleSequence (2 * i)) 1 :=
    convergesTo_subsequence limsupLiminfExample_tailSup_tendsto_one
      ⟨fun i => 2 * i, by
        intro i j hij
        nlinarith⟩
  have hsub_even :
      ConvergesTo (fun i : ℕ => limsupLiminfExampleSequence (2 * i)) 1 := by
    simpa [hconst_even] using hsub_even_sup
  have hnotconv : ¬ ConvergentSequence limsupLiminfExampleSequence := by
    intro hconv
    rcases hconv with ⟨L, hL⟩
    have hodd_lim :
        ConvergesTo (fun i : ℕ => limsupLiminfExampleSequence (2 * i + 1)) L :=
      convergesTo_subsequence (x := limsupLiminfExampleSequence) (l := L) hL
        ⟨fun i => 2 * i + 1, by
          intro i j hij
          nlinarith⟩
    have hodd_eq : L = 0 :=
      convergesTo_unique hodd_lim hodd_const
    have heven_lim :
        ConvergesTo (fun i : ℕ => limsupLiminfExampleSequence (2 * i)) L :=
      convergesTo_subsequence (x := limsupLiminfExampleSequence) (l := L) hL
        ⟨fun i => 2 * i, by
          intro i j hij
          nlinarith⟩
    have heven_eq : L = 1 :=
      convergesTo_unique heven_lim hsub_even
    linarith
  exact ⟨hliminf, hlimsup, hnotconv⟩


/-- Theorem 2.3.4: For a bounded sequence `{x_n}`, there is a subsequence whose
limit equals `limsup_{n → ∞} x_n`, and (possibly another) subsequence whose
limit equals `liminf_{n → ∞} x_n`. -/
theorem subsequence_converging_to_limsup_liminf {x : RealSequence}
    (hx : BoundedSequence x) :
    (∃ s : RealSubsequence x, ConvergesTo (s.asSequence) (limsupSequence x)) ∧
      ∃ s : RealSubsequence x, ConvergesTo (s.asSequence) (liminfSequence x) := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hUpper : ∀ n, x n ≤ B := fun n => (abs_le.mp (hB n)).2
  have hLower : ∀ n, -B ≤ x n := fun n => (abs_le.mp (hB n)).1
  -- helper: approximate a tail supremum by a term of the sequence
  have h_sup_approx :
      ∀ n (ε : ℝ), 0 < ε → ∃ m ≥ n, tailSupSequence x n - x m < ε := by
    intro n ε hε
    classical
    let S : Set ℝ := {y : ℝ | ∃ k ≥ n, y = x k}
    have hnonempty : S.Nonempty := ⟨x n, ⟨n, le_rfl, rfl⟩⟩
    have hBdd : BddAbove S := by
      refine ⟨B, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hUpper k
    have hlt : tailSupSequence x n - ε < tailSupSequence x n :=
      sub_lt_self _ hε
    have hlt' : tailSupSequence x n - ε < sSup S := by
      simpa [tailSupSequence, S] using hlt
    obtain ⟨y, hyS, hygt⟩ := exists_lt_of_lt_csSup hnonempty hlt'
    rcases hyS with ⟨m, hm, rfl⟩
    have hdiff : tailSupSequence x n - x m < ε := by linarith
    exact ⟨m, hm, hdiff⟩
  -- helper: approximate a tail infimum by a term of the sequence
  have h_inf_approx :
      ∀ n (ε : ℝ), 0 < ε → ∃ m ≥ n, x m - tailInfSequence x n < ε := by
    intro n ε hε
    let S : Set ℝ := {y : ℝ | ∃ k ≥ n, y = x k}
    have hnonempty : S.Nonempty := ⟨x n, ⟨n, le_rfl, rfl⟩⟩
    have hBddBelow : BddBelow S := by
      refine ⟨-B, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hLower k
    have hlt : tailInfSequence x n < tailInfSequence x n + ε := by linarith
    obtain ⟨y, hyS, hylt⟩ :=
      exists_lt_of_csInf_lt (hs := hnonempty) (hb := hlt)
    rcases hyS with ⟨m, hm, rfl⟩
    refine ⟨m, hm, ?_⟩
    linarith
  -- indices for the limsup subsequence
  let idx : ℕ → ℕ :=
    fun n =>
      Nat.recOn n (motive := fun _ => ℕ) 0
        (fun k ih =>
          Classical.choose
            (h_sup_approx (ih + 1) ((1 : ℝ) / (k + 2)) (by
              have hpos : 0 < (k + 2 : ℝ) := by nlinarith
              exact one_div_pos.mpr hpos)))
  have hidx_step :
      ∀ k, idx (k + 1) ≥ idx k + 1 ∧
        tailSupSequence x (idx k + 1) - x (idx (k + 1)) < (1 : ℝ) / (k + 2) :=
    by
      intro k
      classical
      have hpos : 0 < (1 : ℝ) / (k + 2) := by
        have hpos' : 0 < (k + 2 : ℝ) := by nlinarith
        exact one_div_pos.mpr hpos'
      have h :=
        Classical.choose_spec
          (h_sup_approx (idx k + 1) ((1 : ℝ) / (k + 2)) hpos)
      have hge : idx (k + 1) ≥ idx k + 1 := by
        simpa [idx] using h.1
      have hclose :
          tailSupSequence x (idx k + 1) - x (idx (k + 1)) <
            (1 : ℝ) / (k + 2) := by
        simpa [idx] using h.2
      exact ⟨hge, hclose⟩
  have hstrict_idx : StrictMono idx := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    have hge := (hidx_step k).1
    exact lt_of_lt_of_le (Nat.lt_succ_self (idx k)) hge
  -- BddAbove witnesses for later use
  have hBddAbove_set :
      ∀ n, BddAbove {y : ℝ | ∃ k ≥ n, y = x k} := by
    intro n
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact hUpper k
  -- reusable properties of the tail extremal sequences
  have hprops := limsup_liminf_properties x ⟨B, hB⟩
  rcases hprops with ⟨hmonoSup, hmonoInf, _, _, _, _, _⟩
  -- boundedness of the tail extremal sequences
  have hBoundSup : BoundedSequence (tailSupSequence x) := by
    refine ⟨B, ?_⟩
    intro n
    have hnonempty :
        ({y : ℝ | ∃ k ≥ n, y = x k}).Nonempty :=
      ⟨x n, ⟨n, le_rfl, rfl⟩⟩
    have hupper : tailSupSequence x n ≤ B := by
      dsimp [tailSupSequence]
      refine csSup_le hnonempty ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hUpper k
    have hmem : x n ∈ {y : ℝ | ∃ k ≥ n, y = x k} := ⟨n, le_rfl, rfl⟩
    have hsup : x n ≤ tailSupSequence x n := by
      have h := le_csSup (hBddAbove_set n) hmem
      simpa [tailSupSequence] using h
    have hlower : -B ≤ tailSupSequence x n := le_trans (hLower n) hsup
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hBoundInf : BoundedSequence (tailInfSequence x) := by
    refine ⟨B, ?_⟩
    intro n
    have hnonempty :
        ({y : ℝ | ∃ k ≥ n, y = x k}).Nonempty :=
      ⟨x n, ⟨n, le_rfl, rfl⟩⟩
    have hBddBelow :
        BddBelow {y : ℝ | ∃ k ≥ n, y = x k} := by
      refine ⟨-B, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hLower k
    have hmem : x n ∈ {y : ℝ | ∃ k ≥ n, y = x k} := ⟨n, le_rfl, rfl⟩
    have hinf : tailInfSequence x n ≤ x n := by
      have h := csInf_le hBddBelow hmem
      simpa [tailInfSequence] using h
    have hupper : tailInfSequence x n ≤ B := le_trans hinf (hUpper n)
    have hge : -B ≤ tailInfSequence x n := by
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hLower k
    exact abs_le.mpr ⟨hge, hupper⟩
  -- inequalities for the difference `tailSup - x` along the subsequence
  have hAntitoneSup : Antitone (tailSupSequence x) :=
    antitone_nat_of_succ_le (by
      intro n
      simpa [Nat.succ_eq_add_one] using hmonoSup n)
  have h_diff_bound :
      ∀ k, |tailSupSequence x (idx (k + 1)) - x (idx (k + 1))| <
        (1 : ℝ) / (k + 2) := by
    intro k
    have hmono :=
      hAntitoneSup ((hidx_step k).1)
    have hle :
        tailSupSequence x (idx (k + 1)) - x (idx (k + 1)) ≤
          tailSupSequence x (idx k + 1) - x (idx (k + 1)) := by linarith
    have hclose := (hidx_step k).2
    have hlt :
        tailSupSequence x (idx (k + 1)) - x (idx (k + 1)) <
          (1 : ℝ) / (k + 2) :=
      lt_of_le_of_lt hle hclose
    have hnonneg :
        0 ≤ tailSupSequence x (idx (k + 1)) - x (idx (k + 1)) := by
      have hmem :
          x (idx (k + 1)) ∈ {y : ℝ | ∃ t ≥ idx (k + 1), y = x t} :=
        ⟨idx (k + 1), le_rfl, rfl⟩
      have hsup :
          x (idx (k + 1)) ≤ tailSupSequence x (idx (k + 1)) := by
        have h := le_csSup (hBddAbove_set (idx (k + 1))) hmem
        simpa [tailSupSequence] using h
      linarith
    have habs : |tailSupSequence x (idx (k + 1)) - x (idx (k + 1))| =
        tailSupSequence x (idx (k + 1)) - x (idx (k + 1)) :=
      abs_of_nonneg hnonneg
    simpa [habs] using hlt
  -- define the error sequence along the subsequence
  let d : RealSequence :=
    fun k => tailSupSequence x (idx k) - x (idx k)
  have hd_nonneg : ∀ k, 0 ≤ d k := by
    intro k
    have hmem : x (idx k) ∈ {y : ℝ | ∃ t ≥ idx k, y = x t} :=
      ⟨idx k, le_rfl, rfl⟩
    have h := le_csSup (hBddAbove_set (idx k)) hmem
    have hsup : x (idx k) ≤ tailSupSequence x (idx k) := by
      simpa [tailSupSequence] using h
    linarith [hsup]
  have hd_bound :
      ∀ k, d (k + 1) ≤ (1 : ℝ) / (k + 2) := by
    intro k
    have hpos :=
      h_diff_bound k
    have hle_abs : d (k + 1) = |d (k + 1)| :=
      (abs_of_nonneg (hd_nonneg (k + 1))).symm
    have hpos' : |d (k + 1)| < (1 : ℝ) / (k + 2) := by
      simpa [d] using hpos
    linarith
  -- the error sequence (shifted) converges to zero by squeeze
  have hconst0 : ConvergesTo (fun _ : ℕ => (0 : ℝ)) 0 :=
    constant_seq_converges 0
  have hinv_shift : ConvergesTo (fun k : ℕ => ((k : ℝ) + 2)⁻¹) 0 := by
    have hconv :
        ConvergesTo (fun n : ℕ => (↑n + 1)⁻¹) 0 := by
      simpa [one_div] using inv_nat_converges_to_zero
    have htail :
        ConvergesTo
          (sequenceTail (fun n : ℕ => (↑n + 1)⁻¹) 0) 0 :=
      by
        simpa [sequenceTail] using
          (convergesTo_tail_of_converges
            (x := fun n : ℕ => (↑n + 1)⁻¹) (K := 0) hconv)
    have htail_simp :
        sequenceTail (fun n : ℕ => (↑n + 1)⁻¹) 0 =
          fun k : ℕ => ((k : ℝ) + 2)⁻¹ := by
      funext k
      simp [sequenceTail]
      ring
    simpa [htail_simp] using htail
  have hd_tail_zero :
      ConvergesTo (fun k : ℕ => d (k + 1)) 0 :=
    squeeze_converges
      (a := fun _ : ℕ => (0 : ℝ))
      (b := fun k : ℕ => ((k : ℝ) + 2)⁻¹)
      (x := fun k : ℕ => d (k + 1)) (l := 0)
      (by intro k; exact hd_nonneg (k + 1))
      (by
        intro k
        have hb := hd_bound k
        simpa [one_div, Nat.cast_add, Nat.cast_one,
          add_comm, add_left_comm, add_assoc] using hb)
      hconst0 hinv_shift
  have hd_zero : ConvergesTo d 0 :=
    convergesTo_of_tail_converges 0 hd_tail_zero
  -- convergence of the tail supremum sequence
  have hconvSupL :
      ConvergesTo (tailSupSequence x) (limsupSequence x) := by
    simpa [limsupSequence] using
      (monotoneDecreasingSequence_tendsto_inf hmonoSup hBoundSup)
  have hconvSup_subseq :
      ConvergesTo (fun k => tailSupSequence x (idx k))
        (limsupSequence x) :=
    convergesTo_subsequence (x := tailSupSequence x) (l := limsupSequence x)
      hconvSupL ⟨idx, hstrict_idx⟩
  -- combine convergences to get the limsup subsequence
  have hsub_eq :
      (fun k => tailSupSequence x (idx k) - d k) =
        fun k => x (idx k) := by
    funext k
    simp [d]
  have hsub_conv :
      ConvergesTo (fun k => x (idx k)) (limsupSequence x) := by
    have h := limit_sub_of_convergent
      (x := fun k => tailSupSequence x (idx k))
      (y := d) (l := limsupSequence x) (m := 0)
      hconvSup_subseq hd_zero
    simpa [hsub_eq] using h
  have h_limsup_subsequence :
      ∃ s : RealSubsequence x,
        ConvergesTo (s.asSequence) (limsupSequence x) :=
    ⟨⟨idx, hstrict_idx⟩, by simpa [RealSubsequence.asSequence] using hsub_conv⟩
  -- indices for the liminf subsequence
  let idxInf : ℕ → ℕ :=
    fun n =>
      Nat.recOn n (motive := fun _ => ℕ) 0
        (fun k ih =>
          Classical.choose
            (h_inf_approx (ih + 1) ((1 : ℝ) / (k + 2)) (by
              have hpos : 0 < (k + 2 : ℝ) := by nlinarith
              exact one_div_pos.mpr hpos)))
  have hidxInf_step :
      ∀ k, idxInf (k + 1) ≥ idxInf k + 1 ∧
        x (idxInf (k + 1)) - tailInfSequence x (idxInf k + 1) <
          (1 : ℝ) / (k + 2) := by
    intro k
    classical
    have hpos : 0 < (1 : ℝ) / (k + 2) := by
      have hpos' : 0 < (k + 2 : ℝ) := by nlinarith
      exact one_div_pos.mpr hpos'
    have h :=
      Classical.choose_spec
        (h_inf_approx (idxInf k + 1) ((1 : ℝ) / (k + 2)) hpos)
    have hge : idxInf (k + 1) ≥ idxInf k + 1 := by
      simpa [idxInf] using h.1
    have hclose :
        x (idxInf (k + 1)) - tailInfSequence x (idxInf k + 1) <
          (1 : ℝ) / (k + 2) := by
      simpa [idxInf] using h.2
    exact ⟨hge, hclose⟩
  have hstrict_idxInf : StrictMono idxInf := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    have hge := (hidxInf_step k).1
    exact lt_of_lt_of_le (Nat.lt_succ_self (idxInf k)) hge
  have hMonotoneInf : Monotone (tailInfSequence x) :=
    monotone_nat_of_le_succ (by
      intro n
      simpa [Nat.succ_eq_add_one] using hmonoInf n)
  have hInf_diff_bound :
      ∀ k, |x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1))| <
        (1 : ℝ) / (k + 2) := by
    intro k
    have hmono := hMonotoneInf ((hidxInf_step k).1)
    have hle :
        x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1)) ≤
          x (idxInf (k + 1)) - tailInfSequence x (idxInf k + 1) := by linarith
    have hclose := (hidxInf_step k).2
    have hlt :
        x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1)) <
          (1 : ℝ) / (k + 2) :=
      lt_of_le_of_lt hle hclose
    have hnonneg :
        0 ≤ x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1)) := by
      have hmem : x (idxInf (k + 1)) ∈
          {y : ℝ | ∃ t ≥ idxInf (k + 1), y = x t} :=
        ⟨idxInf (k + 1), le_rfl, rfl⟩
      have hinf :
          tailInfSequence x (idxInf (k + 1)) ≤ x (idxInf (k + 1)) := by
        have h := csInf_le (by
          refine ⟨-B, ?_⟩
          intro y hy
          rcases hy with ⟨t, ht, rfl⟩
          exact hLower t) hmem
        simpa [tailInfSequence] using h
      linarith
    have habs :
        |x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1))| =
          x (idxInf (k + 1)) - tailInfSequence x (idxInf (k + 1)) :=
      abs_of_nonneg hnonneg
    simpa [habs] using hlt
  -- error sequence for liminf
  let dInf : RealSequence :=
    fun k => x (idxInf k) - tailInfSequence x (idxInf k)
  have hdInf_nonneg : ∀ k, 0 ≤ dInf k := by
    intro k
    have hmem :
        x (idxInf k) ∈ {y : ℝ | ∃ t ≥ idxInf k, y = x t} :=
      ⟨idxInf k, le_rfl, rfl⟩
    have hinf :=
      csInf_le (by
        refine ⟨-B, ?_⟩
        intro y hy
        rcases hy with ⟨t, ht, rfl⟩
        exact hLower t) hmem
    have hle : tailInfSequence x (idxInf k) ≤ x (idxInf k) := by
      simpa [tailInfSequence] using hinf
    linarith
  have hdInf_bound :
      ∀ k, dInf (k + 1) ≤ (1 : ℝ) / (k + 2) := by
    intro k
    have hpos : |dInf (k + 1)| < (1 : ℝ) / (k + 2) := by
      simpa [dInf] using hInf_diff_bound k
    have habs :
        |dInf (k + 1)| = dInf (k + 1) :=
      abs_of_nonneg (hdInf_nonneg (k + 1))
    linarith
  have hdInf_tail_zero :
      ConvergesTo (fun k : ℕ => dInf (k + 1)) 0 :=
    squeeze_converges
      (a := fun _ : ℕ => (0 : ℝ))
      (b := fun k : ℕ => ((k : ℝ) + 2)⁻¹)
      (x := fun k : ℕ => dInf (k + 1)) (l := 0)
      (by intro k; exact hdInf_nonneg (k + 1))
      (by
        intro k
        have hb := hdInf_bound k
        simpa [one_div, Nat.cast_add, Nat.cast_one,
          add_comm, add_left_comm, add_assoc] using hb)
      hconst0 hinv_shift
  have hdInf_zero : ConvergesTo dInf 0 :=
    convergesTo_of_tail_converges 0 hdInf_tail_zero
  have hconvInfL :
      ConvergesTo (tailInfSequence x) (liminfSequence x) := by
    simpa [liminfSequence] using
      (monotoneIncreasingSequence_tendsto_sup hmonoInf hBoundInf)
  have hconvInf_subseq :
      ConvergesTo (fun k => tailInfSequence x (idxInf k))
        (liminfSequence x) :=
    convergesTo_subsequence (x := tailInfSequence x) (l := liminfSequence x)
      hconvInfL ⟨idxInf, hstrict_idxInf⟩
  have hsub_eq_inf :
      (fun k => tailInfSequence x (idxInf k) + dInf k) =
        fun k => x (idxInf k) := by
    funext k
    dsimp [dInf]
    ring
  have hsub_inf_conv :
      ConvergesTo (fun k => x (idxInf k)) (liminfSequence x) := by
    have h := limit_add_of_convergent
      (x := fun k => tailInfSequence x (idxInf k))
      (y := dInf) (l := liminfSequence x) (m := 0)
      hconvInf_subseq hdInf_zero
    simpa [hsub_eq_inf] using h
  have h_liminf_subsequence :
      ∃ s : RealSubsequence x,
        ConvergesTo (s.asSequence) (liminfSequence x) :=
    ⟨⟨idxInf, hstrict_idxInf⟩,
      by simpa [RealSubsequence.asSequence] using hsub_inf_conv⟩
  exact ⟨h_limsup_subsequence, h_liminf_subsequence⟩

/-- Proposition 2.3.5: A bounded sequence `{x_n}` converges if and only if its
limit inferior and limit superior coincide. Moreover, when `{x_n}` converges
to `L`, this common value equals `L`. -/
lemma convergent_iff_liminf_eq_limsup {x : RealSequence} (hx : BoundedSequence x) :
    ConvergentSequence x ↔ liminfSequence x = limsupSequence x := by
  constructor
  · intro hconv
    rcases hconv with ⟨L, hL⟩
    obtain ⟨h_limsup_subseq, h_liminf_subseq⟩ :=
      subsequence_converging_to_limsup_liminf hx
    rcases h_limsup_subseq with ⟨sSup, hSup⟩
    rcases h_liminf_subseq with ⟨sInf, hInf⟩
    have hSup' : ConvergesTo (sSup.asSequence) L :=
      convergesTo_subsequence (x := x) (l := L) hL sSup
    have hInf' : ConvergesTo (sInf.asSequence) L :=
      convergesTo_subsequence (x := x) (l := L) hL sInf
    have hlimsup_eq : L = limsupSequence x :=
      convergesTo_unique hSup' hSup
    have hliminf_eq : L = liminfSequence x :=
      convergesTo_unique hInf' hInf
    calc
      liminfSequence x = L := hliminf_eq.symm
      _ = limsupSequence x := hlimsup_eq
  · intro hEq
    obtain ⟨B, hB⟩ := hx
    have hUpper : ∀ n, x n ≤ B := fun n => (abs_le.mp (hB n)).2
    have hLower : ∀ n, -B ≤ x n := fun n => (abs_le.mp (hB n)).1
    have hmem :
        ∀ n, x n ∈ {y : ℝ | ∃ k ≥ n, y = x k} :=
      fun n => ⟨n, le_rfl, rfl⟩
    have hBddAbove :
        ∀ n, BddAbove {y : ℝ | ∃ k ≥ n, y = x k} := by
      intro n
      refine ⟨B, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hUpper k
    have hBddBelow :
        ∀ n, BddBelow {y : ℝ | ∃ k ≥ n, y = x k} := by
      intro n
      refine ⟨-B, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact hLower k
    have h_inf_le : ∀ n, tailInfSequence x n ≤ x n := by
      intro n
      have h := csInf_le (hBddBelow n) (hmem n)
      simpa [tailInfSequence] using h
    have h_le_sup : ∀ n, x n ≤ tailSupSequence x n := by
      intro n
      have h := le_csSup (hBddAbove n) (hmem n)
      simpa [tailSupSequence] using h
    have hprops := limsup_liminf_properties x ⟨B, hB⟩
    rcases hprops with ⟨hmonoSup, hmonoInf, _, _, hlimsup_eq, hliminf_eq, _⟩
    have hBoundSup : BoundedSequence (tailSupSequence x) := by
      refine ⟨B, ?_⟩
      intro n
      have hnonempty :
          ({y : ℝ | ∃ k ≥ n, y = x k}).Nonempty :=
        ⟨x n, ⟨n, le_rfl, rfl⟩⟩
      have hupper : tailSupSequence x n ≤ B := by
        dsimp [tailSupSequence]
        refine csSup_le hnonempty ?_
        intro y hy
        rcases hy with ⟨k, hk, rfl⟩
        exact hUpper k
      have hmem : x n ∈ {y : ℝ | ∃ k ≥ n, y = x k} := ⟨n, le_rfl, rfl⟩
      have hsup : x n ≤ tailSupSequence x n := by
        have h := le_csSup (hBddAbove n) hmem
        simpa [tailSupSequence] using h
      have hlower : -B ≤ tailSupSequence x n := le_trans (hLower n) hsup
      exact abs_le.mpr ⟨hlower, hupper⟩
    have hBoundInf : BoundedSequence (tailInfSequence x) := by
      refine ⟨B, ?_⟩
      intro n
      have hnonempty :
          ({y : ℝ | ∃ k ≥ n, y = x k}).Nonempty :=
        ⟨x n, ⟨n, le_rfl, rfl⟩⟩
      have hinf : tailInfSequence x n ≤ x n := by
        have h := csInf_le (hBddBelow n) (hmem n)
        simpa [tailInfSequence] using h
      have hupper : tailInfSequence x n ≤ B := le_trans hinf (hUpper n)
      have hge : -B ≤ tailInfSequence x n := by
        refine le_csInf hnonempty ?_
        intro y hy
        rcases hy with ⟨k, hk, rfl⟩
        exact hLower k
      exact abs_le.mpr ⟨hge, hupper⟩
    have hconvSup' :
        ConvergesTo (tailSupSequence x) (limsupSequence x) := by
      have h :=
        monotoneDecreasingSequence_tendsto_inf hmonoSup hBoundSup
      simpa [hlimsup_eq] using h
    have hconvInf' :
        ConvergesTo (tailInfSequence x) (liminfSequence x) := by
      have h :=
        monotoneIncreasingSequence_tendsto_sup hmonoInf hBoundInf
      simpa [hliminf_eq] using h
    have hconv_x :
        ConvergesTo x (limsupSequence x) :=
      squeeze_converges (a := tailInfSequence x) (b := tailSupSequence x)
        (x := x) (l := limsupSequence x)
        (by intro n; exact h_inf_le n)
        (by intro n; exact h_le_sup n)
        (by simpa [hEq] using hconvInf')
        hconvSup'
    exact ⟨limsupSequence x, hconv_x⟩

/-- See Proposition 2.3.5: for a bounded sequence that converges to `L`, the
limit equals both the limit inferior and the limit superior. -/
lemma convergent_limit_eq_limsup_liminf {x : RealSequence} {L : ℝ}
    (hx : BoundedSequence x) (hconv : ConvergesTo x L) :
    liminfSequence x = L ∧ limsupSequence x = L := by
  obtain ⟨h_limsup_subseq, h_liminf_subseq⟩ :=
    subsequence_converging_to_limsup_liminf hx
  rcases h_limsup_subseq with ⟨sSup, hSup⟩
  rcases h_liminf_subseq with ⟨sInf, hInf⟩
  have hSup' : ConvergesTo (sSup.asSequence) L :=
    convergesTo_subsequence (x := x) (l := L) hconv sSup
  have hInf' : ConvergesTo (sInf.asSequence) L :=
    convergesTo_subsequence (x := x) (l := L) hconv sInf
  have hlimsup_eq : limsupSequence x = L :=
    (convergesTo_unique hSup' hSup).symm
  have hliminf_eq : liminfSequence x = L :=
    (convergesTo_unique hInf' hInf).symm
  exact ⟨hliminf_eq, hlimsup_eq⟩

/-- Proposition 2.3.6: For a bounded sequence `{x_n}` and any subsequence
`{x_{n_k}}`, the limit inferior of the original sequence bounds below the
subsequence's limit inferior, which in turn does not exceed its limit
superior, and this limit superior is bounded above by the limit superior of
the original sequence. -/
lemma limsup_liminf_subsequence_bounds {x : RealSequence} (hx : BoundedSequence x)
    (s : RealSubsequence x) :
    liminfSequence x ≤ liminfSequence (s.asSequence) ∧
      liminfSequence (s.asSequence) ≤ limsupSequence (s.asSequence) ∧
        limsupSequence (s.asSequence) ≤ limsupSequence x := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hUpper : ∀ n, x n ≤ B := fun n => (abs_le.mp (hB n)).2
  have hLower : ∀ n, -B ≤ x n := fun n => (abs_le.mp (hB n)).1
  let A : ℕ → Set ℝ := fun n => {y : ℝ | ∃ k ≥ n, y = x k}
  let C : ℕ → Set ℝ := fun n => {y : ℝ | ∃ k ≥ n, y = x (s.indices k)}
  have hNonemptyA : ∀ n, (A n).Nonempty := fun n => ⟨x n, ⟨n, le_rfl, rfl⟩⟩
  have hNonemptyC : ∀ n, (C n).Nonempty :=
    fun n => ⟨x (s.indices n), ⟨n, le_rfl, rfl⟩⟩
  have hBddAboveA : ∀ n, BddAbove (A n) := by
    intro n
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact hUpper k
  have hBddBelowA : ∀ n, BddBelow (A n) := by
    intro n
    refine ⟨-B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact hLower k
  have hBddAboveC : ∀ n, BddAbove (C n) := by
    intro n
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact hUpper (s.indices k)
  have hsubset : ∀ n, C n ⊆ A n := by
    intro n y hy
    rcases hy with ⟨k, hk, rfl⟩
    have hindex : k ≤ s.indices k :=
      subsequence_indices_ge_self (x := x) s k
    exact ⟨s.indices k, le_trans hk hindex, rfl⟩
  have htailSup_le : ∀ n,
      tailSupSequence (s.asSequence) n ≤ tailSupSequence x n := by
    intro n
    have h := csSup_le_csSup (hBddAboveA n) (hNonemptyC n) (hsubset n)
    simpa [tailSupSequence, A, C] using h
  have htailInf_le : ∀ n,
      tailInfSequence x n ≤ tailInfSequence (s.asSequence) n := by
    intro n
    have h := csInf_le_csInf (hBddBelowA n) (hNonemptyC n) (hsubset n)
    simpa [tailInfSequence, A, C] using h
  have hbounded_subseq : BoundedSequence (s.asSequence) := by
    refine ⟨B, ?_⟩
    intro n
    have h := hB (s.indices n)
    simpa [RealSubsequence.asSequence] using h
  -- middle inequality from general liminf/limsup bounds
  have hmid :
      liminfSequence (s.asSequence) ≤ limsupSequence (s.asSequence) := by
    have hprops := limsup_liminf_properties (s.asSequence) hbounded_subseq
    exact hprops.2.2.2.2.2.2
  -- prepare bounds on ranges for limsup comparison
  have hBddBelow_range_supseq :
      BddBelow (Set.range (tailSupSequence (s.asSequence))) := by
    refine ⟨-B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hmem : x (s.indices n) ∈ C n := ⟨n, le_rfl, rfl⟩
    have hge_x : -B ≤ x (s.indices n) := hLower _
    have hsup : x (s.indices n) ≤ tailSupSequence (s.asSequence) n := by
      have h := le_csSup (hBddAboveC n) hmem
      simpa [tailSupSequence, C] using h
    linarith
  have hlimsup_le_tailsup :
      ∀ n, limsupSequence (s.asSequence) ≤
        tailSupSequence (s.asSequence) n := by
    intro n
    have hmem :
        tailSupSequence (s.asSequence) n ∈
          Set.range (tailSupSequence (s.asSequence)) := ⟨n, rfl⟩
    have h := csInf_le hBddBelow_range_supseq hmem
    simpa [limsupSequence] using h
  have hRangeSup_nonempty :
      (Set.range (tailSupSequence x)).Nonempty :=
    ⟨tailSupSequence x 0, ⟨0, rfl⟩⟩
  have hlimsup_subseq_le :
      limsupSequence (s.asSequence) ≤ limsupSequence x := by
    have hle :
        ∀ y ∈ Set.range (tailSupSequence x),
          limsupSequence (s.asSequence) ≤ y := by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact le_trans (hlimsup_le_tailsup n) (htailSup_le n)
    have h := le_csInf hRangeSup_nonempty hle
    simpa [limsupSequence] using h
  -- liminf comparison
  have hBddAbove_range_infs :
      BddAbove (Set.range (tailInfSequence (s.asSequence))) := by
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hmem : x (s.indices n) ∈ C n := ⟨n, le_rfl, rfl⟩
    have hinf : tailInfSequence (s.asSequence) n ≤ x (s.indices n) := by
      have h := csInf_le (by
        refine ⟨-B, ?_⟩
        intro y hy
        rcases hy with ⟨k, hk, rfl⟩
        exact hLower (s.indices k)) hmem
      simpa [tailInfSequence, C] using h
    exact le_trans hinf (by simpa using hUpper _)
  have htailInf_le_liminf :
      ∀ n, tailInfSequence x n ≤ liminfSequence (s.asSequence) := by
    intro n
    have hmem :
        tailInfSequence (s.asSequence) n ∈
          Set.range (tailInfSequence (s.asSequence)) := ⟨n, rfl⟩
    have hle_sup :
        tailInfSequence (s.asSequence) n ≤ liminfSequence (s.asSequence) := by
      have h := le_csSup hBddAbove_range_infs hmem
      simpa [liminfSequence] using h
    exact le_trans (htailInf_le n) hle_sup
  have hRangeInf_nonempty :
      (Set.range (tailInfSequence x)).Nonempty :=
    ⟨tailInfSequence x 0, ⟨0, rfl⟩⟩
  have hliminf_le :
      liminfSequence x ≤ liminfSequence (s.asSequence) := by
    have h :=
      csSup_le hRangeInf_nonempty (by
        intro y hy
        rcases hy with ⟨n, rfl⟩
        exact htailInf_le_liminf n)
    simpa [liminfSequence] using h
  exact ⟨hliminf_le, hmid, hlimsup_subseq_le⟩

/-- Theorem 2.3.8 (Bolzano--Weierstrass): Every bounded real sequence
`{x_n}` admits a convergent subsequence `{x_{n_i}}`. -/
theorem bolzanoWeierstrass_real_sequence {x : RealSequence}
    (hx : BoundedSequence x) :
    ∃ s : RealSubsequence x, ConvergentSequence (s.asSequence) := by
  classical
  -- bound the sequence inside a compact interval
  obtain ⟨B, hB⟩ := hx
  have hmem : ∀ n, x n ∈ Set.Icc (-B) B := by
    intro n
    have h := hB n
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
  -- compactness of the closed interval yields a convergent subsequence
  rcases (isCompact_Icc.tendsto_subseq (x := fun n => x n) hmem) with
    ⟨l, _hl, φ, hmono, hφ⟩
  let s : RealSubsequence x := ⟨φ, hmono⟩
  refine ⟨s, ?_⟩
  refine ⟨l, ?_⟩
  -- translate the filter convergence statement to the ε–`M` notion
  have hφ' :
      Filter.Tendsto (s.asSequence) Filter.atTop (nhds l) := by
    simpa [s, RealSubsequence.asSequence] using hφ
  exact (convergesTo_iff_tendsto (x := s.asSequence) (l := l)).2 hφ'

/-- Proposition 2.3.7: A bounded sequence `{x_n}` converges to `x` if and only if
every convergent subsequence `{x_{n_k}}` converges to the same limit `x`. -/
lemma converges_iff_convergent_subsequences_converge
    {x : RealSequence} {l : ℝ} (hx : BoundedSequence x) :
    ConvergesTo x l ↔
      ∀ s : RealSubsequence x,
        ConvergentSequence (s.asSequence) → ConvergesTo (s.asSequence) l := by
  constructor
  · intro hconv s _hsconv
    exact convergesTo_subsequence (x := x) (l := l) hconv s
  · intro hsub
    classical
    -- assume the sequence does not converge to `l` and derive a contradiction
    by_contra hnot
    -- extract a uniform gap from the definition of `ConvergesTo`
    have hε :
        ∃ ε > 0, ∀ M, ∃ n ≥ M, ε ≤ |x n - l| := by
      have hneg : ¬ ConvergesTo x l := hnot
      unfold ConvergesTo at hneg
      push_neg at hneg
      rcases hneg with ⟨ε, hεpos, hfail⟩
      refine ⟨ε, hεpos, ?_⟩
      intro M
      rcases hfail M with ⟨n, hn, hlt⟩
      refine ⟨n, hn, ?_⟩
      exact hlt
    rcases hε with ⟨ε, hεpos, hfar⟩
    -- build a subsequence whose terms stay `ε` away from `l`
    let idx : ℕ → ℕ :=
      fun n =>
        Nat.recOn n (Classical.choose (hfar 0))
          (fun k ih =>
            Classical.choose (hfar (ih + 1)))
    have hidx_step :
        ∀ k, idx (k + 1) ≥ idx k + 1 ∧ ε ≤ |x (idx (k + 1)) - l| := by
      intro k
      have hspec := Classical.choose_spec (hfar (idx k + 1))
      rcases hspec with ⟨hge, hdist⟩
      exact ⟨hge, hdist⟩
    have hidx_base : ε ≤ |x (idx 0) - l| :=
      (Classical.choose_spec (hfar 0)).2
    have hfar_idx : ∀ n, ε ≤ |x (idx n) - l| := by
      intro n
      induction' n with n ih
      · simpa using hidx_base
      · simpa using (hidx_step n).2
    have hstrict : StrictMono idx := by
      refine strictMono_nat_of_lt_succ ?_
      intro k
      have hge := (hidx_step k).1
      have hlt : idx k < idx k + 1 := Nat.lt_succ_self _
      exact lt_of_lt_of_le hlt hge
    let s₀ : RealSubsequence x := ⟨idx, hstrict⟩
    -- the constructed subsequence remains bounded
    rcases hx with ⟨B, hB⟩
    have hBound_s₀ : BoundedSequence (s₀.asSequence) := by
      refine ⟨B, ?_⟩
      intro n
      simpa [RealSubsequence.asSequence, s₀] using hB (idx n)
    -- apply Bolzano--Weierstrass to obtain a convergent sub-subsequence
    rcases bolzanoWeierstrass_real_sequence (x := s₀.asSequence) hBound_s₀ with
      ⟨t, hconv_t⟩
    rcases hconv_t with ⟨L, hL⟩
    -- promote the sub-subsequence to a subsequence of the original sequence
    let u : RealSubsequence x :=
      ⟨fun n => s₀.indices (t.indices n),
        s₀.strictlyIncreasing.comp t.strictlyIncreasing⟩
    have hu_seq :
        u.asSequence = t.asSequence := by
      funext n
      rfl
    have hconv_u : ConvergesTo (u.asSequence) L := by
      -- `u.asSequence` definally agrees with `t.asSequence`
      simpa [hu_seq] using hL
    -- use the hypothesis to force convergence of this subsequence to `l`
    have hconv_to_l : ConvergesTo (u.asSequence) l :=
      hsub u ⟨L, hconv_u⟩
    -- contradiction: every term of `u` stays at least `ε` away from `l`
    have hfar_u : ∀ n, ε ≤ |u.asSequence n - l| := by
      intro n
      dsimp [u, RealSubsequence.asSequence, s₀, idx]
      exact hfar_idx (t.indices n)
    have hεpos' : 0 < ε / 2 := by linarith
    rcases hconv_to_l (ε / 2) hεpos' with ⟨M, hM⟩
    have hcontr := hfar_u M
    have hclose := hM M le_rfl
    have hlt : |u.asSequence M - l| < ε := by
      have hhalf : |u.asSequence M - l| < ε / 2 := hclose
      linarith
    exact (not_lt_of_ge hcontr) hlt

/-- Definition 2.3.9: A real sequence `{x_n}` diverges to `+∞` if for every
`K : ℝ` there exists `M : ℕ` such that `x n > K` for all `n ≥ M`; we then
write `lim_{n → ∞} x_n = ∞`. It diverges to `-∞` if for every `K : ℝ` there
is `M : ℕ` with `x n < K` for all `n ≥ M`, written `lim_{n → ∞} x_n = -∞`. -/
def DivergesToInfinitySequence (x : RealSequence) : Prop :=
  ∀ K : ℝ, ∃ M : ℕ, ∀ n ≥ M, K < x n

/-- A real sequence diverges to negative infinity when its terms eventually
stay below every real threshold. -/
def DivergesToMinusInfinitySequence (x : RealSequence) : Prop :=
  ∀ K : ℝ, ∃ M : ℕ, ∀ n ≥ M, x n < K

/-- Proposition 2.3.10: A monotone unbounded sequence diverges to an infinite
limit. If `{x_n}` is monotone increasing and unbounded above, then
`lim_{n → ∞} x_n = ∞`; if it is monotone decreasing and unbounded below, then
`lim_{n → ∞} x_n = -∞`. -/
lemma monotone_unbounded_diverges_to_infinity {x : RealSequence}
    (hx : MonotoneIncreasingSequence x) (h_unbounded : ¬ BoundedAboveSequence x) :
    DivergesToInfinitySequence x := by
  classical
  -- lack of an upper bound gives indices with arbitrarily large values
  have hlarge : ∀ K : ℝ, ∃ n : ℕ, K < x n := by
    dsimp [BoundedAboveSequence] at h_unbounded
    push_neg at h_unbounded
    intro K
    rcases h_unbounded K with ⟨n, hn⟩
    exact ⟨n, hn⟩
  -- monotonicity propagates the lower estimate to all later terms
  have hmono : Monotone x := monotone_nat_of_le_succ hx
  intro K
  rcases hlarge K with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hle : x M ≤ x n := hmono hn
  exact lt_of_lt_of_le hM hle

/-- See Proposition 2.3.10: a monotone decreasing sequence without a lower
bound diverges to `-∞`. -/
lemma monotone_unbounded_diverges_to_minus_infinity {x : RealSequence}
    (hx : MonotoneDecreasingSequence x) (h_unbounded : ¬ BoundedBelowSequence x) :
    DivergesToMinusInfinitySequence x := by
  classical
  have hsmall : ∀ K : ℝ, ∃ n : ℕ, x n < K := by
    dsimp [BoundedBelowSequence] at h_unbounded
    push_neg at h_unbounded
    intro K
    rcases h_unbounded K with ⟨n, hn⟩
    exact ⟨n, hn⟩
  have hmono : Antitone x :=
    antitone_nat_of_succ_le (by
      intro n
      simpa [Nat.succ_eq_add_one] using hx n)
  intro K
  rcases hsmall K with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hle : x n ≤ x M := hmono hn
  exact lt_of_le_of_lt hle hM

/-- The book's notion of divergence to `+∞` agrees with `Filter.Tendsto` to
`Filter.atTop`. -/
lemma divergesToInfinity_iff_tendsto_atTop (x : RealSequence) :
    DivergesToInfinitySequence x ↔
      Filter.Tendsto x Filter.atTop Filter.atTop := by
  constructor
  · intro h
    refine Filter.tendsto_atTop.2 ?_
    intro K
    rcases h K with ⟨M, hM⟩
    refine Filter.eventually_atTop.2 ?_
    refine ⟨M, ?_⟩
    intro n hn
    exact le_of_lt (hM n hn)
  · intro h K
    have h' := Filter.tendsto_atTop.1 h (K + 1)
    rcases Filter.eventually_atTop.1 h' with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n hn
    have hle : K + 1 ≤ x n := hM n hn
    have hlt : K < K + 1 := by linarith
    exact lt_of_lt_of_le hlt hle

/-- The book's notion of divergence to `-∞` agrees with `Filter.Tendsto` to
`Filter.atBot`. -/
lemma divergesToMinusInfinity_iff_tendsto_atBot (x : RealSequence) :
    DivergesToMinusInfinitySequence x ↔
      Filter.Tendsto x Filter.atTop Filter.atBot := by
  constructor
  · intro h
    refine Filter.tendsto_atBot.2 ?_
    intro K
    rcases h K with ⟨M, hM⟩
    refine Filter.eventually_atTop.2 ?_
    refine ⟨M, ?_⟩
    intro n hn
    exact le_of_lt (hM n hn)
  · intro h K
    have h' := Filter.tendsto_atBot.1 h (K - 1)
    rcases Filter.eventually_atTop.1 h' with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n hn
    have hle : x n ≤ K - 1 := hM n hn
    have hlt : x n < K := by linarith
    exact hlt

/-- Example 2.3.11: the sequences `n` and `n^2` diverge to `+∞`, while the
sequence `-n` diverges to `-∞`. -/
lemma example_2311_limits :
    DivergesToInfinitySequence (fun n : ℕ => (n : ℝ)) ∧
      DivergesToInfinitySequence (fun n : ℕ => (n : ℝ) ^ 2) ∧
        DivergesToMinusInfinitySequence (fun n : ℕ => - (n : ℝ)) := by
  have hnat :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro K
    obtain ⟨M, hM⟩ := exists_nat_gt K
    refine Filter.eventually_atTop.2 ?_
    refine ⟨M, ?_⟩
    intro n hn
    have hlt : K < (n : ℝ) := by
      have hM' : K < (M : ℝ) := by exact_mod_cast hM
      have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact lt_of_lt_of_le hM' hMn
    exact le_of_lt hlt
  have hsquare :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro K
    obtain ⟨M, hM⟩ := exists_nat_gt (|K| + 1)
    refine Filter.eventually_atTop.2 ?_
    refine ⟨M, ?_⟩
    intro n hn
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hgt_abs : |K| < (n : ℝ) := by
      have hM' : |K| + 1 < (M : ℝ) := by exact_mod_cast hM
      linarith
    have hgtK : K < (n : ℝ) := lt_of_le_of_lt (le_abs_self K) hgt_abs
    have hone_le : (1 : ℝ) ≤ (n : ℝ) := by
      have hMpos : (1 : ℝ) ≤ (M : ℝ) := by
        have habs : (1 : ℝ) ≤ |K| + 1 := by nlinarith [abs_nonneg K]
        have hM' : |K| + 1 < (M : ℝ) := by exact_mod_cast hM
        linarith
      exact le_trans hMpos hMn
    have hle_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    exact le_trans (le_of_lt hgtK) hle_sq
  have hneg :
      Filter.Tendsto (fun n : ℕ => - (n : ℝ))
        Filter.atTop Filter.atBot := by
    -- compose with neg tending to `atBot`
    exact Filter.tendsto_neg_atTop_atBot.comp hnat
  refine
    ⟨(divergesToInfinity_iff_tendsto_atTop _).2 hnat,
      ⟨(divergesToInfinity_iff_tendsto_atTop _).2 hsquare,
        (divergesToMinusInfinity_iff_tendsto_atBot _).2 hneg⟩⟩

/-- Definition 2.3.12: For an unbounded real sequence `{xₙ}`, set
`aₙ = sup { x_k | k ≥ n }` and `bₙ = inf { x_k | k ≥ n }`, where the suprema and
infima are taken in the extended real numbers. The limit superior is
`inf { aₙ : n ∈ ℕ }` and the limit inferior is `sup { bₙ : n ∈ ℕ }`. -/
noncomputable def tailSupSequenceEReal (x : RealSequence) (n : ℕ) : EReal :=
  sSup {y : EReal | ∃ k ≥ n, y = (x k : EReal)}

/-- See the preceding comment: the lower tail infimum in the extended reals. -/
noncomputable def tailInfSequenceEReal (x : RealSequence) (n : ℕ) : EReal :=
  sInf {y : EReal | ∃ k ≥ n, y = (x k : EReal)}

/-- The limit superior of a (possibly unbounded) real sequence, valued in `ℝ∞`. -/
noncomputable def limsupSequenceEReal (x : RealSequence) : EReal :=
  sInf (Set.range (tailSupSequenceEReal x))

/-- The limit inferior of a (possibly unbounded) real sequence, valued in `ℝ∞`. -/
noncomputable def liminfSequenceEReal (x : RealSequence) : EReal :=
  sSup (Set.range (tailInfSequenceEReal x))

/-- The extended-real limsup defined via tail suprema coincides with the
`Filter.limsup` of the sequence viewed in `ℝ∞`. -/
lemma limsupSequenceEReal_eq_filter_limsup (x : RealSequence) :
    limsupSequenceEReal x =
      Filter.limsup (fun n => (x n : EReal)) Filter.atTop := by
  classical
  -- rewrite the tail supremum in terms of a two-parameter `iSup`
  have htail :
      ∀ n, tailSupSequenceEReal x n = ⨆ k ≥ n, (x k : EReal) := by
    intro n
    apply le_antisymm
    · -- any element of the tail is bounded above by the `iSup`
      refine sSup_le ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
    · -- the `iSup` is bounded above by the tail supremum
      refine iSup₂_le ?_
      intro k hk
      have hmem :
          (x k : EReal) ∈ {y : EReal | ∃ t ≥ n, y = (x t : EReal)} :=
        ⟨k, hk, rfl⟩
      exact le_sSup hmem
  -- identify the `sInf` of the range with an `iInf`
  have hInf :
      limsupSequenceEReal x = ⨅ n, tailSupSequenceEReal x n := by
    simp [limsupSequenceEReal, sInf_range]
  calc
    limsupSequenceEReal x
        = ⨅ n, tailSupSequenceEReal x n := hInf
    _ = ⨅ n, ⨆ k ≥ n, (x k : EReal) := by
      refine iInf_congr ?_
      intro n
      exact htail n
    _ = Filter.limsup (fun n => (x n : EReal)) Filter.atTop := by
      symm
      exact Filter.limsup_eq_iInf_iSup_of_nat (u := fun n => (x n : EReal))

/-- The extended-real liminf defined via tail infima coincides with the
`Filter.liminf` of the sequence viewed in `ℝ∞`. -/
lemma liminfSequenceEReal_eq_filter_liminf (x : RealSequence) :
    liminfSequenceEReal x =
      Filter.liminf (fun n => (x n : EReal)) Filter.atTop := by
  classical
  -- rewrite the tail infimum using a two-parameter `iInf`
  have htail :
      ∀ n, tailInfSequenceEReal x n = ⨅ k ≥ n, (x k : EReal) := by
    intro n
    apply le_antisymm
    · -- the tail infimum is a lower bound for every tail term
      refine le_iInf ?_
      intro k
      refine le_iInf ?_
      intro hk
      have hmem :
          (x k : EReal) ∈ {y : EReal | ∃ t ≥ n, y = (x t : EReal)} :=
        ⟨k, hk, rfl⟩
      exact sInf_le hmem
    · -- the `iInf` is a lower bound for the tail, hence below its infimum
      have hnonempty :
          ({y : EReal | ∃ k ≥ n, y = (x k : EReal)}).Nonempty :=
        ⟨(x n : EReal), ⟨n, le_rfl, rfl⟩⟩
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      -- `⨅ k ≥ n, x k` is bounded above by its `k`-th summand
      exact
        le_trans
          (iInf_le (fun k => ⨅ _ : k ≥ n, (x k : EReal)) k)
          (iInf_le (fun _ : k ≥ n => (x k : EReal)) hk)
  -- identify the `sSup` of the range with an `iSup`
  have hSup :
      liminfSequenceEReal x = ⨆ n, tailInfSequenceEReal x n := by
    simp [liminfSequenceEReal, sSup_range]
  calc
    liminfSequenceEReal x
        = ⨆ n, tailInfSequenceEReal x n := hSup
    _ = ⨆ n, ⨅ k ≥ n, (x k : EReal) := by
      refine iSup_congr ?_
      intro n
      exact htail n
    _ = Filter.liminf (fun n => (x n : EReal)) Filter.atTop := by
      symm
      exact Filter.liminf_eq_iSup_iInf_of_nat (u := fun n => (x n : EReal))

/-- Proposition 2.3.13: For an unbounded sequence `{x_n}` with tail suprema
`a_n = sup { x_k | k ≥ n }` and tail infima `b_n = inf { x_k | k ≥ n }`
formed in the extended reals, the sequence `{a_n}` is decreasing and `{b_n}`
is increasing. If every `a_n` is a (finite) real number, then
`limsup_{n → ∞} x_n = lim_{n → ∞} a_n`; if every `b_n` is real, then
`liminf_{n → ∞} x_n = lim_{n → ∞} b_n`. -/
lemma limsup_liminf_unbounded_properties (x : RealSequence)
    (_hx : ¬ BoundedSequence x) :
    Antitone (tailSupSequenceEReal x) ∧
      Monotone (tailInfSequenceEReal x) ∧
        (∀ _hfinite : ∀ n, ∃ r : ℝ, tailSupSequenceEReal x n = (r : EReal),
          ∃ l : EReal,
            Filter.Tendsto (fun n => tailSupSequenceEReal x n)
              Filter.atTop (nhds l) ∧
              limsupSequenceEReal x = l) ∧
        (∀ _hfinite : ∀ n, ∃ r : ℝ, tailInfSequenceEReal x n = (r : EReal),
          ∃ l : EReal,
            Filter.Tendsto (fun n => tailInfSequenceEReal x n)
              Filter.atTop (nhds l) ∧
              liminfSequenceEReal x = l) := by
  classical
  have hAntitone : Antitone (tailSupSequenceEReal x) := by
    intro m n hmn
    dsimp [tailSupSequenceEReal]
    refine sSup_le_sSup ?_
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact ⟨k, le_trans hmn hk, rfl⟩
  have hMonotone : Monotone (tailInfSequenceEReal x) := by
    intro m n hmn
    dsimp [tailInfSequenceEReal]
    refine sInf_le_sInf ?_
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact ⟨k, le_trans hmn hk, rfl⟩
  refine ⟨hAntitone, hMonotone, ?_, ?_⟩
  · intro _hfinite
    refine ⟨limsupSequenceEReal x, ?_, rfl⟩
    simpa [limsupSequenceEReal] using
      (tendsto_atTop_iInf (f := fun n => tailSupSequenceEReal x n) hAntitone)
  · intro _hfinite
    refine ⟨liminfSequenceEReal x, ?_, rfl⟩
    simpa [liminfSequenceEReal] using
      (tendsto_atTop_iSup (f := fun n => tailInfSequenceEReal x n) hMonotone)

/-- Example 2.3.14: For `xₙ = 0` when `n` is odd and `xₙ = n` when `n` is
even, each tail supremum `aₙ` equals `∞` because even indices keep growing,
while each tail infimum `bₙ` is `0` thanks to the odd indices. Consequently,
`limsup_{n → ∞} xₙ = ∞`, `liminf_{n → ∞} xₙ = 0`, and the sequence is
divergent. -/
def example2314Sequence : RealSequence := fun n => if Even n then (n : ℝ) else 0

lemma example2314_tailSup_tailInf :
    (∀ n, tailSupSequenceEReal example2314Sequence n = (⊤ : EReal)) ∧
      (∀ n, tailInfSequenceEReal example2314Sequence n = (0 : EReal)) := by
  classical
  constructor
  · intro n
    -- use `eq_top_iff_forall_lt`
    have hlt : ∀ r : ℝ, (r : EReal) < tailSupSequenceEReal example2314Sequence n := by
      intro r
      obtain ⟨m, hmr⟩ := exists_nat_gt r
      let k : ℕ := 2 * max m n
      have hk_even : Even k := by
        dsimp [k]
        exact Nat.even_mul.2 (Or.inl (by decide))
      have hk_ge : k ≥ n := by
        dsimp [k]
        have hmax : n ≤ max m n := le_max_right _ _
        have hpos : max m n ≤ 2 * max m n := by nlinarith
        exact le_trans hmax hpos
      have hr_lt_k : r < k := by
        have hm_le_max : m ≤ max m n := le_max_left _ _
        have hmax_le_k : max m n ≤ k := by
          dsimp [k]
          nlinarith
        have hm_le_k_nat : m ≤ k := le_trans hm_le_max hmax_le_k
        have hm_le_k : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm_le_k_nat
        exact lt_of_lt_of_le hmr hm_le_k
      have hmem :
          (example2314Sequence k : EReal) ∈
            {y : EReal | ∃ t ≥ n, y = (example2314Sequence t : EReal)} :=
        ⟨k, hk_ge, rfl⟩
      have hk_le :
          (example2314Sequence k : EReal) ≤
            tailSupSequenceEReal example2314Sequence n := by
        have := le_sSup (s := {y : EReal | ∃ t ≥ n, y = (example2314Sequence t : EReal)}) hmem
        simpa [tailSupSequenceEReal] using this
      have hk_val : example2314Sequence k = k := by
        simp [example2314Sequence, hk_even]
      have hr_lt_val : (r : EReal) < (example2314Sequence k : EReal) := by
        have : (r : EReal) < (k : EReal) := by exact_mod_cast hr_lt_k
        simpa [hk_val] using this
      exact lt_of_lt_of_le hr_lt_val hk_le
    exact (EReal.eq_top_iff_forall_lt (tailSupSequenceEReal example2314Sequence n)).2 hlt
  · intro n
    -- every tail contains an odd index giving value `0`, and all values are nonnegative
    have hmem_zero :
        (0 : EReal) ∈ {y : EReal | ∃ k ≥ n, y = (example2314Sequence k : EReal)} := by
      refine ⟨2 * n + 1, ?_, ?_⟩
      · nlinarith
      · have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
        have hEven : ¬ Even (2 * n + 1) := (Nat.not_even_iff_odd.mpr hodd)
        simp [example2314Sequence, hEven]
    have hLower :
        ∀ y ∈ {y : EReal | ∃ k ≥ n, y = (example2314Sequence k : EReal)}, (0 : EReal) ≤ y := by
      intro y hy
      rcases hy with ⟨k, _, rfl⟩
      by_cases hk : Even k
      · have hk_nonneg : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
        have hval : example2314Sequence k = k := by simp [example2314Sequence, hk]
        have hk_nonneg' : (0 : EReal) ≤ (k : ℝ) := by exact_mod_cast hk_nonneg
        convert hk_nonneg' using 1
        simp [hval]
      · simp [example2314Sequence, hk]
    have hle : tailInfSequenceEReal example2314Sequence n ≤ (0 : EReal) := by
      have := sInf_le (s := {y : EReal | ∃ k ≥ n, y = (example2314Sequence k : EReal)}) hmem_zero
      simpa [tailInfSequenceEReal] using this
    have hge : (0 : EReal) ≤ tailInfSequenceEReal example2314Sequence n := by
      have :=
        le_sInf (a := (0 : EReal))
          (by intro y hy; exact hLower y hy)
      simpa [tailInfSequenceEReal] using this
    exact le_antisymm hle hge

lemma example2314_limsup_liminf :
    limsupSequenceEReal example2314Sequence = (⊤ : EReal) ∧
      liminfSequenceEReal example2314Sequence = (0 : EReal) ∧
        ¬ ConvergentSequence example2314Sequence := by
  classical
  have htails := example2314_tailSup_tailInf
  have hsup := htails.1
  have hinf := htails.2
  have hbounded : ¬ BoundedSequence example2314Sequence := by
    intro hB
    rcases hB with ⟨B, hB⟩
    obtain ⟨m, hm⟩ := exists_nat_gt B
    have hB' := hB (2 * m)
    have hEven : Even (2 * m) := Nat.even_mul.2 (Or.inl (by decide))
    have hval : example2314Sequence (2 * m) = (2 * m : ℝ) := by
      simp [example2314Sequence, hEven]
    have hlt : |example2314Sequence (2 * m)| ≤ B := hB'
    have hcontr : ¬ |(2 * m : ℝ)| ≤ B := by
      have hpos : (0 : ℝ) ≤ (2 * m : ℝ) := by exact_mod_cast Nat.zero_le (2 * m)
      have habs : |(2 * m : ℝ)| = (2 * m : ℝ) := abs_of_nonneg hpos
      have hm' : (B : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hgt : (2 * m : ℝ) > B := by nlinarith
      simpa [habs] using not_le_of_gt hgt
    exact hcontr (by simpa [hval] using hlt)
  have hlimsup :
      limsupSequenceEReal example2314Sequence = (⊤ : EReal) := by
    have hrange : Set.range (tailSupSequenceEReal example2314Sequence) = {⊤} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨n, rfl⟩
        simp [hsup n]
      · intro hx
        rcases hx with rfl
        exact ⟨0, by simp [hsup]⟩
    simp [limsupSequenceEReal, hrange]
  have hliminf :
      liminfSequenceEReal example2314Sequence = (0 : EReal) := by
    have hrange : Set.range (tailInfSequenceEReal example2314Sequence) = {0} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨n, rfl⟩
        simp [hinf n]
      · intro hx
        rcases hx with rfl
        exact ⟨0, by simp [hinf]⟩
    simp [liminfSequenceEReal, hrange]
  have hnotconv : ¬ ConvergentSequence example2314Sequence := by
    intro hconv
    have hbd : BoundedSequence example2314Sequence :=
      convergentSequence_bounded hconv
    exact hbounded hbd
  exact ⟨hlimsup, hliminf, hnotconv⟩

end Section03
end Chap02
