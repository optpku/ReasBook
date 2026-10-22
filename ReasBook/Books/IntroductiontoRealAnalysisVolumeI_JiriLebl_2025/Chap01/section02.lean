/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

universe u v

section Chap01
section Section02

/-- Theorem 1.2.1: There exists an ordered field `ℝ` with the least-upper-bound
property containing the rationals `ℚ`; such a structure is unique up to an
order-preserving field isomorphism. -/
theorem real_exists_complete_ordered_field :
    ∃ (R : Type) (hF : Field R) (hL : LinearOrder R) (hS : IsStrictOrderedRing R), by
      let _ : Field R := hF
      let _ : LinearOrder R := hL
      let _ : IsStrictOrderedRing R := hS
      exact
        (∀ {E : Set R}, E.Nonempty → BddAbove E → ∃ supE, IsLUB E supE) ∧
          Function.Injective (fun q : ℚ => (q : R)) := by
  refine ⟨ℝ, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · intro E hE hEb
    refine ⟨sSup E, isLUB_csSup hE hEb⟩
  · exact Rat.cast_injective

/-- Any two ordered fields with the least-upper-bound property that contain
the rationals are isomorphic as ordered fields. -/
theorem real_unique_complete_ordered_field
    (R : Type u) [Field R] [ConditionallyCompleteLinearOrder R] [IsStrictOrderedRing R]
    (S : Type v) [Field S] [ConditionallyCompleteLinearOrder S] [IsStrictOrderedRing S] :
    Nonempty (R ≃+* S) := by
  classical
  refine ⟨(LinearOrderedField.inducedOrderRingIso R S).toRingEquiv⟩

/-- Proposition 1.2.2: If a real number `x` satisfies `x ≤ ε` for every `ε > 0`,
then `x ≤ 0`. -/
theorem real_le_zero_of_le_pos {x : ℝ} (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  by_contra hx
  have hxpos : 0 < x := lt_of_not_ge hx
  have h' : x ≤ x / 2 := h (x / 2) (half_pos hxpos)
  have : x < x := lt_of_le_of_lt h' (half_lt_self hxpos)
  exact (lt_irrefl _ this)

/-- Example 1.2.3: There exists a unique positive real number `r` such that
`r ^ 2 = 2`; this number is denoted `√2`. -/
theorem exists_unique_pos_sq_eq_two : ∃! r : ℝ, 0 < r ∧ r ^ 2 = (2 : ℝ) := by
  refine ⟨Real.sqrt 2, ?_, ?_⟩
  · constructor
    · exact Real.sqrt_pos.2 (by norm_num)
    · simp
  · intro r hr
    rcases hr with ⟨hrpos, hrpow⟩
    have h := congrArg Real.sqrt hrpow
    have h_abs : |r| = Real.sqrt 2 := by
      simpa [Real.sqrt_sq_eq_abs] using h
    have hr_abs : r = |r| := (abs_of_pos hrpos).symm
    calc
      r = |r| := hr_abs
      _ = Real.sqrt 2 := h_abs

/-- The book's notation `√2` realized via the mathlib square root. -/
noncomputable def sqrtTwo : ℝ := Real.sqrt 2

/-- The element `sqrtTwo` is positive and squares to `2`, matching the defining
property of `√2`. -/
lemma sqrtTwo_spec : 0 < sqrtTwo ∧ sqrtTwo ^ 2 = (2 : ℝ) := by
  constructor
  · exact Real.sqrt_pos.2 (by norm_num)
  · simp [sqrtTwo]

/-- Uniqueness of the positive square root of `2`. -/
lemma sqrtTwo_unique {r : ℝ} (hr : 0 < r ∧ r ^ 2 = (2 : ℝ)) : r = sqrtTwo := by
  obtain ⟨r₀, hr₀, huniq⟩ := exists_unique_pos_sq_eq_two
  have hr_eq : r = r₀ := huniq _ hr
  have hsqrt_eq : sqrtTwo = r₀ := huniq _ sqrtTwo_spec
  exact hr_eq.trans hsqrt_eq.symm

/-- Theorem 1.2.4:
(i) (Archimedean property) If `x, y ∈ ℝ` with `x > 0`, then there exists
`n ∈ ℕ` such that `n * x > y`.
(ii) (`ℚ` is dense in `ℝ`) If `x, y ∈ ℝ` with `x < y`, then there exists
`r ∈ ℚ` such that `x < r < y`. -/
theorem archimedean_and_rat_dense :
    (∀ x y : ℝ, 0 < x → ∃ n : ℕ, (n : ℝ) * x > y) ∧
      (∀ x y : ℝ, x < y → ∃ r : ℚ, x < (r : ℝ) ∧ (r : ℝ) < y) := by
  constructor
  · intro x y hx
    rcases exists_nat_gt (y / x) with ⟨n, hn⟩
    have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
    have h' : (y / x) * x < (n : ℝ) * x :=
      mul_lt_mul_of_pos_right hn hx
    have h'' : (y / x) * x = y := by field_simp [hxne]
    refine ⟨n, ?_⟩
    simpa [h''] using h'
  · intro x y hxy
    rcases exists_rat_btwn hxy with ⟨r, hrx, hry⟩
    exact ⟨r, hrx, hry⟩

/-- Corollary 1.2.5: The infimum of the set `{1 / n : n ∈ ℕ}` is `0`. -/
theorem inf_nat_inv_eq_zero :
    sInf (Set.range fun n : ℕ => (1 : ℝ) / (n.succ : ℝ)) = (0 : ℝ) := by
  classical
  set A : Set ℝ := Set.range fun n : ℕ => (1 : ℝ) / (n.succ : ℝ)
  have hA_nonempty : A.Nonempty := ⟨1, ⟨0, by simp⟩⟩
  have hA_lower : ∀ x ∈ A, 0 ≤ x := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    positivity
  have hA_nonneg : 0 ≤ sInf A := le_csInf hA_nonempty hA_lower
  have hA_le : ∀ ε > 0, sInf A ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ) / ε)
    have hlt : (1 : ℝ) / ε < (n.succ : ℝ) :=
      lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
    have hpos : 0 < (1 : ℝ) / ε := one_div_pos.mpr hε
    have hdiv_succ : (1 : ℝ) / (n.succ : ℝ) < ε := by
      have h := one_div_lt_one_div_of_lt hpos hlt
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hε
      have h_inv : (1 : ℝ) / ((1 : ℝ) / ε) = ε := by field_simp [hεne]
      simpa [h_inv] using h
    have hmem : (1 : ℝ) / (n.succ : ℝ) ∈ A := ⟨n, by simp⟩
    have hcsInf : sInf A ≤ (1 : ℝ) / (n.succ : ℝ) :=
      csInf_le ⟨0, hA_lower⟩ hmem
    exact le_trans hcsInf (le_of_lt hdiv_succ)
  have hA_le_zero : sInf A ≤ 0 := real_le_zero_of_le_pos hA_le
  have hA_eq : sInf A = 0 := le_antisymm hA_le_zero hA_nonneg
  simpa [A] using hA_eq

/-- Proposition 1.2.6: Let `A ⊆ ℝ` be nonempty.
(i) If `A` is bounded above, then `sup (x + A) = x + sup A`.
(ii) If `A` is bounded below, then `inf (x + A) = x + inf A`.
(iii) If `x > 0` and `A` is bounded above, then `sup (x * A) = x * sup A`.
(iv) If `x > 0` and `A` is bounded below, then `inf (x * A) = x * inf A`.
(v) If `x < 0` and `A` is bounded below, then `sup (x * A) = x * inf A`.
(vi) If `x < 0` and `A` is bounded above, then `inf (x * A) = x * sup A`. -/
theorem sup_inf_arithmetic {A : Set ℝ} (hA : A.Nonempty) :
    (∀ x, BddAbove A → sSup ((fun a => x + a) '' A) = x + sSup A) ∧
      (∀ x, BddBelow A → sInf ((fun a => x + a) '' A) = x + sInf A) ∧
        (∀ {x : ℝ}, 0 < x → BddAbove A →
          sSup ((fun a => x * a) '' A) = x * sSup A) ∧
          (∀ {x : ℝ}, 0 < x → BddBelow A →
            sInf ((fun a => x * a) '' A) = x * sInf A) ∧
            (∀ {x : ℝ}, x < 0 → BddBelow A →
              sSup ((fun a => x * a) '' A) = x * sInf A) ∧
              (∀ {x : ℝ}, x < 0 → BddAbove A →
                sInf ((fun a => x * a) '' A) = x * sSup A) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hAub
    rcases hAub with ⟨b, hb⟩
    have hAub' : BddAbove A := ⟨b, hb⟩
    have hBnonempty : ((fun a => x + a) '' A).Nonempty := hA.image _
    have hBb : BddAbove ((fun a => x + a) '' A) := by
      refine ⟨x + b, ?_⟩
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      have : a ≤ b := hb ha
      linarith
    have h_le : sSup ((fun a => x + a) '' A) ≤ x + sSup A := by
      refine csSup_le hBnonempty ?_
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      have : a ≤ sSup A := le_csSup hAub' ha
      linarith
    have h_sup_le : sSup A ≤ sSup ((fun a => x + a) '' A) - x := by
      refine csSup_le hA ?_
      intro y hy
      have hy' : x + y ≤ sSup ((fun a => x + a) '' A) :=
        le_csSup hBb ⟨y, hy, rfl⟩
      linarith
    have h_ge : x + sSup A ≤ sSup ((fun a => x + a) '' A) := by
      linarith
    exact le_antisymm h_le h_ge
  · intro x hAlb
    rcases hAlb with ⟨b, hb⟩
    have hAlb' : BddBelow A := ⟨b, hb⟩
    have hBnonempty : ((fun a => x + a) '' A).Nonempty := hA.image _
    have hBb : BddBelow ((fun a => x + a) '' A) := by
      refine ⟨x + b, ?_⟩
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      have : b ≤ a := hb ha
      linarith
    have h_lb : ∀ z ∈ (fun a => x + a) '' A, x + sInf A ≤ z := by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      have : sInf A ≤ a := csInf_le hAlb' ha
      linarith
    have h_ge : x + sInf A ≤ sInf ((fun a => x + a) '' A) :=
      le_csInf hBnonempty h_lb
    have h_lbA : ∀ a ∈ A, sInf ((fun a => x + a) '' A) - x ≤ a := by
      intro a ha
      have hmem : x + a ∈ (fun a => x + a) '' A := ⟨a, ha, rfl⟩
      have hle : sInf ((fun a => x + a) '' A) ≤ x + a := csInf_le hBb hmem
      linarith
    have h_le : sInf ((fun a => x + a) '' A) ≤ x + sInf A := by
      have h := le_csInf hA h_lbA
      linarith
    exact le_antisymm h_le h_ge
  · intro x hx hAub
    have h := Real.sSup_smul_of_nonneg hx.le A
    simpa [smul_eq_mul] using h
  · intro x hx hAlb
    have h := Real.sInf_smul_of_nonneg hx.le A
    simpa [smul_eq_mul] using h
  · intro x hx hAlb
    have h := Real.sSup_smul_of_nonpos hx.le A
    simpa [smul_eq_mul] using h
  · intro x hx hAub
    have h := Real.sInf_smul_of_nonpos hx.le A
    simpa [smul_eq_mul] using h

/-- Proposition 1.2.7: If nonempty sets `A, B ⊆ ℝ` satisfy `x ≤ y` whenever
`x ∈ A` and `y ∈ B`, then `A` is bounded above, `B` is bounded below, and
`sSup A ≤ sInf B`. -/
theorem sup_le_inf_of_forall_le {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ x ∈ A, ∀ y ∈ B, x ≤ y) :
    BddAbove A ∧ BddBelow B ∧ sSup A ≤ sInf B := by
  classical
  have hAub : BddAbove A := by
    rcases hB with ⟨y0, hy0⟩
    refine ⟨y0, ?_⟩
    intro x hx
    exact h x hx y0 hy0
  have hBbl : BddBelow B := by
    rcases hA with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    intro y hy
    exact h x0 hx0 y hy
  have hsup_inf : sSup A ≤ sInf B := by
    apply csSup_le hA
    intro x hx
    exact le_csInf hB (by
      intro y hy
      exact h x hx y hy)
  exact ⟨hAub, hBbl, hsup_inf⟩

/-- Proposition 1.2.8: If `S ⊆ ℝ` is nonempty and bounded above, then for every
`ε > 0` there exists `x ∈ S` with `sSup S - ε < x ≤ sSup S`. -/
lemma exists_mem_between_sub_sup {S : Set ℝ} (hS : S.Nonempty) (hSb : BddAbove S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x ∧ x ≤ sSup S := by
  classical
  have hlt : sSup S - ε < sSup S := by linarith
  obtain ⟨x, hxS, hx⟩ := exists_lt_of_lt_csSup hS hlt
  have hxle : x ≤ sSup S := le_csSup hSb hxS
  exact ⟨x, hxS, hx, hxle⟩

/-- Definition 1.2.9: For a subset `A ⊆ ℝ`, extend `sup` and `inf` to the extended
reals so that (i) `sup ∅ = -∞`, (ii) if `A` is unbounded above then `sup A = ∞`,
(iii) `inf ∅ = ∞`, and (iv) if `A` is unbounded below then `inf A = -∞`. These
agree with `sSup` and `sInf` on `EReal` when we view `A` as a set of extended real
numbers. -/
noncomputable def extendedSup (A : Set ℝ) : EReal :=
  sSup (Set.image (fun x : ℝ => (x : EReal)) A)

/-- (i) The extended supremum of the empty set is `-∞`. -/
lemma extendedSup_empty : extendedSup (∅ : Set ℝ) = (⊥ : EReal) := by
  simp [extendedSup]

/-- (ii) If a set of reals is not bounded above, its extended supremum is `∞`. -/
lemma extendedSup_not_bddAbove {A : Set ℝ} (hA : ¬ BddAbove A) :
    extendedSup A = (⊤ : EReal) := by
  classical
  have h_unbounded : ∀ n : ℕ, ∃ x ∈ A, (n : ℝ) < x := by
    have h := not_bddAbove_iff.1 hA
    intro n
    rcases h (n : ℝ) with ⟨x, hxA, hx⟩
    exact ⟨x, hxA, hx⟩
  have h_nat_le : ∀ n : ℕ, (n : EReal) ≤ extendedSup A := by
    intro n
    obtain ⟨x, hxA, hxgt⟩ := h_unbounded n
    have htop : BddAbove (Set.image (fun x : ℝ => (x : EReal)) A) :=
      ⟨⊤, by intro y hy; exact le_top⟩
    have hxle : (x : EReal) ≤ extendedSup A := by
      have hxmem : (x : EReal) ∈ Set.image (fun x : ℝ => (x : EReal)) A :=
        ⟨x, hxA, rfl⟩
      simpa [extendedSup] using le_csSup htop hxmem
    exact (EReal.coe_le_coe_iff.mpr (le_of_lt hxgt)).trans hxle
  by_contra hne
  have hlt : extendedSup A < (⊤ : EReal) := lt_top_iff_ne_top.mpr hne
  obtain ⟨r, hSup_lt, hr_lt_top⟩ := (EReal.lt_iff_exists_real_btwn).1 hlt
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hchain : extendedSup A < extendedSup A :=
    lt_of_lt_of_le (lt_trans hSup_lt (by exact_mod_cast hn)) (h_nat_le n)
  exact lt_irrefl _ hchain

/-- The extended infimum of a set of reals, computed in `EReal`. -/
noncomputable def extendedInf (A : Set ℝ) : EReal :=
  sInf (Set.image (fun x : ℝ => (x : EReal)) A)

/-- (iii) The extended infimum of the empty set is `∞`. -/
lemma extendedInf_empty : extendedInf (∅ : Set ℝ) = (⊤ : EReal) := by
  simp [extendedInf]

/-- (iv) If a set of reals is not bounded below, its extended infimum is `-∞`. -/
lemma extendedInf_not_bddBelow {A : Set ℝ} (hA : ¬ BddBelow A) :
    extendedInf A = (⊥ : EReal) := by
  classical
  have h_unbounded : ∀ n : ℕ, ∃ x ∈ A, x < -(n : ℝ) := by
    have h := not_bddBelow_iff.1 hA
    intro n
    rcases h (-(n : ℝ)) with ⟨x, hxA, hx⟩
    exact ⟨x, hxA, hx⟩
  have h_lt : ∀ n : ℕ, extendedInf A < (-(n : ℝ) : EReal) := by
    intro n
    obtain ⟨x, hxA, hxlt⟩ := h_unbounded n
    have hbot : BddBelow (Set.image (fun x : ℝ => (x : EReal)) A) :=
      ⟨⊥, by intro y hy; exact bot_le⟩
    have hle : extendedInf A ≤ (x : EReal) := by
      have hxmem : (x : EReal) ∈ Set.image (fun x : ℝ => (x : EReal)) A :=
        ⟨x, hxA, rfl⟩
      simpa [extendedInf] using csInf_le hbot hxmem
    exact lt_of_le_of_lt hle (by exact_mod_cast hxlt)
  by_contra hne
  have hbot_lt : (⊥ : EReal) < extendedInf A :=
    lt_of_le_of_ne bot_le (Ne.symm hne)
  obtain ⟨r, hr_bot, hr⟩ := (EReal.lt_iff_exists_real_btwn).1 hbot_lt
  obtain ⟨n, hn⟩ := exists_nat_gt (-r)
  have hneg : (-(n : ℝ) : EReal) < (r : EReal) := by
    have hn' : -(n : ℝ) < r := by
      simpa [neg_neg] using (neg_lt_neg hn)
    exact_mod_cast hn'
  have hchain : (r : EReal) < (r : EReal) :=
    lt_trans (lt_trans hr (h_lt n)) hneg
  exact lt_irrefl _ hchain

end Section02
end Chap01
