/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open InformationTheory
open scoped BigOperators

universe u v

/-- A prefix code on an alphabet `E` with code alphabet `α` is an assignment of codewords such
that no codeword is a prefix of a different one. -/
structure PrefixCode (α : Type v) (E : Type u) where
  encode : E → List α
  prefix_free : Pairwise (fun e₁ e₂ ↦ ¬ (encode e₁ <+: encode e₂))

namespace PrefixCode

variable {α : Type v} {E : Type u}

-- Proof sketch: if two symbols had the same codeword, that common codeword would be a prefix of
-- the other one, contradicting prefix-freeness.
/-- Prefix-freeness forces the encoding map of a prefix code to be injective. -/
theorem injective (C : PrefixCode α E) : Function.Injective C.encode := by
  intro e₁ e₂ hencode
  by_contra hne
  exact (C.prefix_free hne) (hencode ▸ by simp)

/-- The image of a prefix code is uniquely decodable as a set of codewords. -/
theorem uniquelyDecodable (C : PrefixCode α E) (hε : ∀ e, C.encode e ≠ []) :
    UniquelyDecodable (Set.range C.encode) := by
  -- Route correction: prefix-freeness alone does not force unique decodability if the empty
  -- codeword occurs, so the standard cancellation proof needs the nonempty-codeword hypothesis.
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ _ h₂ hflat
      cases L₂ with
      | nil => rfl
      | cons w₂ t₂ =>
          rcases h₂ w₂ (by simp) with ⟨e₂, rfl⟩
          -- The empty concatenation cannot equal a word starting with a nonempty codeword.
          simp [hε e₂] at hflat
  | cons w₁ t₁ ih =>
      intro L₂ h₁ h₂ hflat
      rcases h₁ w₁ (by simp) with ⟨e₁, rfl⟩
      cases L₂ with
      | nil =>
          -- A nonempty first codeword prevents the whole concatenation from being empty.
          simp [hε e₁] at hflat
      | cons w₂ t₂ =>
          rcases h₂ w₂ (by simp) with ⟨e₂, rfl⟩
          let W := C.encode e₁ ++ t₁.flatten
          have hW : W = C.encode e₂ ++ t₂.flatten := hflat
          have hcompare : C.encode e₁ <+: C.encode e₂ ∨ C.encode e₂ <+: C.encode e₁ := by
            by_cases hlen : (C.encode e₁).length ≤ (C.encode e₂).length
            · left
              have htake₁ : W.take (C.encode e₁).length = C.encode e₁ := by
                simp [W]
              have htake₂ : W.take (C.encode e₂).length = C.encode e₂ := by
                rw [hW]
                simp
              rw [← htake₁, ← htake₂]
              exact (List.take_isPrefix_take).2 (Or.inl hlen)
            · right
              have hlen' : (C.encode e₂).length ≤ (C.encode e₁).length := le_of_not_ge hlen
              have htake₁ : W.take (C.encode e₁).length = C.encode e₁ := by
                simp [W]
              have htake₂ : W.take (C.encode e₂).length = C.encode e₂ := by
                rw [hW]
                simp
              rw [← htake₂, ← htake₁]
              exact (List.take_isPrefix_take).2 (Or.inl hlen')
          have heq : e₁ = e₂ := by
            by_contra hne
            cases hcompare with
            | inl hprefix => exact (C.prefix_free hne) hprefix
            | inr hprefix => exact (C.prefix_free (fun h ↦ hne h.symm)) hprefix
          subst heq
          -- After identifying the first symbol, cancel the common first codeword and recurse.
          have htail : t₁.flatten = t₂.flatten := by
            exact (List.append_right_injective (C.encode e₁)) hflat
          have h₁tail : ∀ w ∈ t₁, w ∈ Set.range C.encode := by
            intro w hw
            exact h₁ w (by simp [hw])
          have h₂tail : ∀ w ∈ t₂, w ∈ Set.range C.encode := by
            intro w hw
            exact h₂ w (by simp [hw])
          simpa using congrArg (List.cons (C.encode e₁)) (ih _ h₁tail h₂tail htail)

variable [Fintype E]

/-- The expected length of a prefix code with respect to a source law `p`. -/
noncomputable def expectedLength (C : PrefixCode α E) (p : PMF E) : ℝ :=
  ∑ e : E, (p e).toReal * (C.encode e).length

-- Proof sketch: unfold `expectedLength`.
/-- The expected code length is the `p`-weighted sum of the codeword lengths. -/
@[simp] theorem expectedLength_def (C : PrefixCode α E) (p : PMF E) :
    C.expectedLength p = ∑ e : E, (p e).toReal * (C.encode e).length := rfl

end PrefixCode

variable {E : Type u}

/-- Helper for Theorem 5.27: if a prefix code contains the empty word, then there can be no
second symbol, because `[]` is a prefix of every codeword. -/
private theorem subsingleton_of_empty_codeword (C : PrefixCode Bool E) {e₀ : E}
    (he₀ : C.encode e₀ = []) : Subsingleton E := by
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  have hone : ∀ e : E, e = e₀ := by
    intro e
    by_contra hne
    have hempty : C.encode e₀ <+: C.encode e := by simpa [he₀]
    exact (C.prefix_free (fun h ↦ hne h.symm)) hempty
  simp [hone e₁, hone e₂]

/-- Helper for Theorem 5.27: the binary Kraft sum of a prefix code is at most `1`. -/
theorem prefixCode_kraft_sum_le_one [Fintype E] (C : PrefixCode Bool E) :
    ∑ e : E, ((1 / 2 : ℝ) ^ (C.encode e).length) ≤ 1 := by
  classical
  by_cases hε : ∃ e, C.encode e = []
  · rcases hε with ⟨e₀, he₀⟩
    have hsub : Subsingleton E := subsingleton_of_empty_codeword C he₀
    letI : Subsingleton E := hsub
    letI : Unique E :=
      { default := e₀
        uniq := fun e ↦ Subsingleton.elim _ _ }
    -- In the degenerate singleton case, the Kraft sum is exactly `1`.
    have hdefault : C.encode default = [] := by simpa using he₀
    simpa [hdefault] using
      (show ((2 : ℝ) ^ (C.encode default).length)⁻¹ ≤ (1 : ℝ) by simp)
  · have hnonempty : ∀ e, C.encode e ≠ [] := by
      intro e he
      exact hε ⟨e, he⟩
    have hud :
        UniquelyDecodable
          ((Finset.image C.encode (Finset.univ : Finset E) : Finset (List Bool)) : Set (List Bool)) := by
      simpa using (C.uniquelyDecodable hnonempty)
    have hk :
        ∑ w ∈ Finset.image C.encode (Finset.univ : Finset E),
            (1 / (Fintype.card Bool : ℝ)) ^ w.length ≤ 1 :=
      kraft_mcmillan_inequality hud
    -- Reindex the Kraft sum from distinct codewords back to the source alphabet.
    rw [Finset.sum_image C.injective.injOn] at hk
    simpa using hk

/-- Helper for Theorem 5.27: the finite binary cross-entropy sum against the code weights
`2^{-length}` is exactly the expected code length. -/
theorem binary_crossEntropy_codeweight_eq_expectedLength [Fintype E]
    (p : PMF E) (C : PrefixCode Bool E) :
    (-∑ e : E, (p e).toReal * Real.logb 2 ((1 / 2 : ℝ) ^ (C.encode e).length) : ℝ) =
      C.expectedLength p := by
  -- Evaluate the logarithm of the dyadic code weight termwise and fold the result into the
  -- expected-length definition.
  rw [← Finset.sum_neg_distrib, PrefixCode.expectedLength_def]
  apply Finset.sum_congr rfl
  intro e _
  rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
  ring

/-- Helper for Theorem 5.27: each base-`2` logarithmic ratio controls the corresponding linear
mass deficit from below. -/
private theorem binaryLogRatio_term_lower_bound (a q : ℝ) (ha : 0 ≤ a) (hq : 0 < q) :
    ((Real.log 2)⁻¹) * (a - q) ≤ a * (Real.logb 2 a - Real.logb 2 q) := by
  by_cases ha0 : a = 0
  · subst ha0
    -- When the source mass vanishes, the right-hand side is zero and the left-hand side is
    -- nonpositive because the comparison mass is strictly positive.
    have hcoef_nonneg : 0 ≤ (Real.log 2)⁻¹ := by positivity
    have hleft : ((Real.log 2)⁻¹) * (0 - q) ≤ 0 := by
      nlinarith
    simpa using hleft
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    have hratio_pos : 0 < q / a := div_pos hq ha_pos
    have hlog_bound : Real.log (q / a) ≤ q / a - 1 :=
      Real.log_le_sub_one_of_pos hratio_pos
    have hneglog_bound : 1 - q / a ≤ -Real.log (q / a) := by
      linarith
    have hscaled :
        (a * (Real.log 2)⁻¹) * (1 - q / a) ≤
          (a * (Real.log 2)⁻¹) * (-Real.log (q / a)) := by
      exact mul_le_mul_of_nonneg_left hneglog_bound (by positivity)
    have hdiv : a * (q / a) = q := by
      field_simp [ha_pos.ne']
    have hratio : a * (1 - q / a) = a - q := by
      rw [mul_sub, hdiv]
      ring
    -- Rewrite the linear and logarithmic sides into the same ratio normal form.
    calc
      ((Real.log 2)⁻¹) * (a - q) = (a * (Real.log 2)⁻¹) * (1 - q / a) := by
        calc
          ((Real.log 2)⁻¹) * (a - q) = (Real.log 2)⁻¹ * (a * (1 - q / a)) := by
            rw [hratio]
          _ = (a * (Real.log 2)⁻¹) * (1 - q / a) := by ring
      _ ≤ (a * (Real.log 2)⁻¹) * (-Real.log (q / a)) := hscaled
      _ = a * (-Real.logb 2 (q / a)) := by
        rw [Real.logb]
        ring
      _ = a * (Real.logb 2 a - Real.logb 2 q) := by
        rw [Real.logb_div hq.ne' ha_pos.ne']
        ring

/-- Helper for Theorem 5.27: on a finite alphabet, every strictly positive sub-probability `q`
dominates the binary entropy in the weighted logarithmic sum `-∑ p_e log₂ q_e`. -/
private theorem binaryEntropy_le_logSum_of_subprobability [Fintype E]
    (p : PMF E) (q : E → ℝ) (hq_pos : ∀ e, 0 < q e) (hq_sum : ∑ e : E, q e ≤ 1) :
    (binaryEntropy p).toReal ≤ -∑ e : E, (p e).toReal * Real.logb 2 (q e) := by
  have hterm :
      ∀ e : E,
        ((Real.log 2)⁻¹) * ((p e).toReal - q e) ≤
          (p e).toReal * (Real.logb 2 (p e).toReal - Real.logb 2 (q e)) := by
    intro e
    exact binaryLogRatio_term_lower_bound (p e).toReal (q e) ENNReal.toReal_nonneg (hq_pos e)
  have hsum_term :
      ∑ e : E, ((Real.log 2)⁻¹) * ((p e).toReal - q e) ≤
        ∑ e : E, (p e).toReal * (Real.logb 2 (p e).toReal - Real.logb 2 (q e)) := by
    exact Finset.sum_le_sum fun e _ ↦ hterm e
  have hsum_p : ∑ e : E, (p e).toReal = 1 := by
    -- Rewrite the finite sum as a `tsum` and use the standard `ENNReal.toReal` summation formula.
    have htsum :
        (∑' e : E, p e).toReal = ∑' e : E, (p e).toReal :=
      ENNReal.tsum_toReal_eq fun e ↦ p.apply_ne_top e
    rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
    simpa using htsum.symm
  have hleft_nonneg :
      0 ≤ ∑ e : E, ((Real.log 2)⁻¹) * ((p e).toReal - q e) := by
    have hcoef_nonneg : 0 ≤ (Real.log 2)⁻¹ := by positivity
    calc
      0 ≤ (Real.log 2)⁻¹ * (1 - ∑ e : E, q e) := by
        exact mul_nonneg hcoef_nonneg (sub_nonneg.mpr hq_sum)
      _ = (Real.log 2)⁻¹ * ((∑ e : E, (p e).toReal) - ∑ e : E, q e) := by
        rw [hsum_p]
      _ = (Real.log 2)⁻¹ * ∑ e : E, ((p e).toReal - q e) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ e : E, ((Real.log 2)⁻¹) * ((p e).toReal - q e) := by
        rw [Finset.mul_sum]
  have hgap_nonneg :
      0 ≤
        (-∑ e : E, (p e).toReal * Real.logb 2 (q e)) -
          (-∑ e : E, (p e).toReal * Real.logb 2 (p e).toReal) := by
    calc
      0 ≤ ∑ e : E, (p e).toReal * (Real.logb 2 (p e).toReal - Real.logb 2 (q e)) :=
        le_trans hleft_nonneg hsum_term
      _ = ∑ e : E,
            ((p e).toReal * Real.logb 2 (p e).toReal - (p e).toReal * Real.logb 2 (q e)) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = (∑ e : E, (p e).toReal * Real.logb 2 (p e).toReal) -
            ∑ e : E, (p e).toReal * Real.logb 2 (q e) := by
        rw [Finset.sum_sub_distrib]
      _ = (-∑ e : E, (p e).toReal * Real.logb 2 (q e)) -
            (-∑ e : E, (p e).toReal * Real.logb 2 (p e).toReal) := by
        ring
  have hineq :
      (-∑ e : E, (p e).toReal * Real.logb 2 (p e).toReal) ≤
        -∑ e : E, (p e).toReal * Real.logb 2 (q e) :=
    sub_nonneg.mp hgap_nonneg
  -- Reinsert the finite Shannon sum for the entropy term.
  rw [binaryEntropy_toReal_eq_sum p]
  exact hineq

-- Proof sketch: set `q_e = 2 ^ (-(C.encode e).length : ℤ)` and use the prefix-free hypothesis to
-- obtain the Kraft inequality; then apply the logarithmic lower bound from Lemma 5.26 to compare
-- `∑ p_e length(C(e))` with `-∑ p_e log₂ p_e`.
/-- Lower-bound part of Theorem 5.27: the expected length of any binary prefix code is at least
the binary entropy of the source distribution. -/
theorem binaryEntropy_le_expectedLength_of_prefixCode [Fintype E]
    (p : PMF E) (C : PrefixCode Bool E) :
    (binaryEntropy p).toReal ≤ C.expectedLength p := by
  let q : E → ℝ := fun e ↦ ((1 / 2 : ℝ) ^ (C.encode e).length)
  have hq_pos : ∀ e : E, 0 < q e := by
    intro e
    simp [q]
  have hq_sum : ∑ e : E, q e ≤ 1 := by
    simpa [q] using prefixCode_kraft_sum_le_one C
  have hcross :
      (binaryEntropy p).toReal ≤
        -∑ e : E, (p e).toReal * Real.logb 2 (q e) :=
    binaryEntropy_le_logSum_of_subprobability p q hq_pos hq_sum
  -- The code weights `q_e = 2^{-length(C(e))}` turn the logarithmic sum into the expected code
  -- length.
  simpa [q] using hcross.trans_eq (binary_crossEntropy_codeweight_eq_expectedLength p C)

/-- Helper for Theorem 5.27: on a finite alphabet, the real masses of a probability mass function
sum to `1`. -/
private theorem sum_toReal_pmf [Fintype E] (p : PMF E) :
    ∑ e : E, (p e).toReal = 1 := by
  -- Rewrite the finite sum as a `tsum` and use the standard `ENNReal.toReal` summation formula.
  have htsum :
      (∑' e : E, p e).toReal = ∑' e : E, (p e).toReal :=
    ENNReal.tsum_toReal_eq fun e ↦ p.apply_ne_top e
  rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
  simpa using htsum.symm

/-- Helper for Theorem 5.27: when a source symbol is split into two equally weighted branches,
its binary logarithm gains exactly one extra bit. -/
private theorem logb_half (x : ℝ) (hx : 0 < x) :
    Real.logb 2 (x / 2) = Real.logb 2 x - 1 := by
  -- The base-`2` logarithm turns division by `2` into subtraction of `1`.
  rw [Real.logb_div hx.ne' two_ne_zero]
  simp [Real.logb_self_eq_one one_lt_two]

/-- Helper for Theorem 5.27: if a positive atom `x` is split in half, then the corresponding
cross-entropy contribution increases by exactly `x`. -/
private theorem neg_mul_logb_half (x : ℝ) (hx : 0 < x) :
    -x * Real.logb 2 (x / 2) = -x * Real.logb 2 x + x := by
  -- Substitute the logarithmic identity for halving and simplify the resulting linear term.
  rw [logb_half x hx]
  ring

/-- Helper for Theorem 5.27: there is a strictly positive comparison mass function `q` on the full
alphabet whose total mass is at most `1` and whose binary cross-entropy exceeds the source entropy
by at most one bit. -/
theorem exists_positive_subprobability_for_source_coding [Fintype E] (p : PMF E) :
    ∃ q : E → ℝ, (∀ e, 0 < q e) ∧ (∑ e : E, q e ≤ 1) ∧
      (-∑ e : E, (p e).toReal * Real.logb 2 (q e) ≤ (binaryEntropy p).toReal + 1) := by
  classical
  by_cases hfull : ∀ e, p e ≠ 0
  · let q : E → ℝ := fun e ↦ (p e).toReal
    refine ⟨q, ?_, ?_, ?_⟩
    · -- On the full-support branch, the source itself is already a strictly positive comparison law.
      intro e
      exact ENNReal.toReal_pos (hfull e) (p.apply_ne_top e)
    · -- The real masses of `p` sum to `1`.
      exact le_of_eq (by simpa [q] using sum_toReal_pmf p)
    · -- With `q = p`, the binary cross-entropy is exactly the binary entropy.
      have hEq : -∑ e : E, (p e).toReal * Real.logb 2 (q e) = (binaryEntropy p).toReal := by
        simpa [q] using (binaryEntropy_toReal_eq_sum p).symm
      linarith
  · push Not at hfull
    rcases hfull with ⟨z₀, hz₀⟩
    have hpos_atom : ∃ e₀, 0 < (p e₀).toReal := by
      by_contra hnone
      push Not at hnone
      have hsum_zero : (∑ e : E, (p e).toReal) = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        exact le_antisymm (hnone e) ENNReal.toReal_nonneg
      have hsum_one : (∑ e : E, (p e).toReal) = 1 := sum_toReal_pmf p
      linarith
    rcases hpos_atom with ⟨e₀, he₀⟩
    let Z : Finset E := Finset.univ.filter fun e ↦ p e = 0
    let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
    let x : ℝ := (p e₀).toReal
    let δ : ℝ := x / (2 * (Z.card + 1))
    let q : E → ℝ := fun e ↦
      if hp : p e = 0 then δ else if e = e₀ then x / 2 else (p e).toReal
    have hx_nonneg : 0 ≤ x := le_of_lt he₀
    have he₀_ne_zero : p e₀ ≠ 0 := by
      intro hp
      simp [x, hp] at he₀
    have he₀_mem_NZ : e₀ ∈ NZ := by
      simp [NZ, he₀_ne_zero]
    refine ⟨q, ?_, ?_, ?_⟩
    · -- Zero-mass symbols receive a tiny uniform reserve, while one positive atom is halved.
      intro e
      by_cases hp : p e = 0
      · simp [q, hp, δ]
        positivity
      · by_cases he : e = e₀
        · subst he
          simp [q, he₀_ne_zero, x]
          positivity
        · simp [q, hp, he, x]
          exact ENNReal.toReal_pos hp (p.apply_ne_top e)
    · -- Splitting over zero and nonzero symbols shows that the total mass stays at most `1`.
      have hsum_zero_part : Finset.sum Z q = (Z.card : ℝ) * δ := by
        calc
          Finset.sum Z q = Finset.sum Z (fun _ ↦ δ) := by
            apply Finset.sum_congr rfl
            intro e he
            have hp : p e = 0 := by simpa [Z] using he
            simp [q, hp]
          _ = (Z.card : ℝ) * δ := by simp
      have hsum_nonzero_p : Finset.sum NZ (fun e ↦ (p e).toReal) = 1 := by
        have hsplit :
            Finset.sum Z (fun e ↦ (p e).toReal) + Finset.sum NZ (fun e ↦ (p e).toReal) = 1 := by
          calc
            Finset.sum Z (fun e ↦ (p e).toReal) + Finset.sum NZ (fun e ↦ (p e).toReal) =
                ∑ e : E, (p e).toReal := by
              simpa [Z, NZ] using
                (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
                  (fun e ↦ (p e).toReal))
            _ = 1 := sum_toReal_pmf p
        have hzero_mass : Finset.sum Z (fun e ↦ (p e).toReal) = 0 := by
          calc
            Finset.sum Z (fun e ↦ (p e).toReal) = Finset.sum Z (fun _ ↦ (0 : ℝ)) := by
              apply Finset.sum_congr rfl
              intro e he
              have hp : p e = 0 := by simpa [Z] using he
              simp [hp]
            _ = 0 := by simp
        linarith
      have hsum_nonzero_part :
          Finset.sum NZ q = x / 2 + Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) := by
        calc
          Finset.sum NZ q = Finset.sum NZ (fun e ↦ if e = e₀ then x / 2 else (p e).toReal) := by
            apply Finset.sum_congr rfl
            intro e he
            have hp : p e ≠ 0 := by simpa [NZ] using he
            by_cases he : e = e₀
            · subst he
              simp [q, he₀_ne_zero, x]
            · simp [q, hp, he, x]
          _ = x / 2 + Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) := by
            have herase :
                Finset.sum (NZ.erase e₀) (fun e ↦ if e = e₀ then x / 2 else (p e).toReal) =
                  Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) := by
              apply Finset.sum_congr rfl
              intro e he
              have he' : e ≠ e₀ := (Finset.mem_erase.mp he).1
              simp [he']
            rw [← Finset.sum_erase_add NZ
              (fun e ↦ if e = e₀ then x / 2 else (p e).toReal) he₀_mem_NZ]
            rw [herase]
            simpa [add_comm, add_left_comm, add_assoc]
      have hsum_nonzero_split :
          Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) + x = 1 := by
        calc
          Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) + x =
              Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal) + (p e₀).toReal := by
            rfl
          _ = Finset.sum NZ (fun e ↦ (p e).toReal) := by
            rw [Finset.sum_erase_add NZ (fun e ↦ (p e).toReal) he₀_mem_NZ]
          _ = 1 := hsum_nonzero_p
      have hreserve_le : (Z.card : ℝ) * δ ≤ x / 2 := by
        have hden_pos : 0 < (2 : ℝ) * (Z.card + 1) := by positivity
        dsimp [δ]
        rw [show ((Z.card : ℝ) * (x / (2 * (Z.card + 1 : ℝ))) : ℝ) =
            ((Z.card : ℝ) * x) / (2 * (Z.card + 1 : ℝ)) by ring]
        rw [div_le_iff₀ hden_pos]
        nlinarith
      calc
        ∑ e : E, q e = Finset.sum Z q + Finset.sum NZ q := by
          symm
          simpa [Z, NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0) q)
        _ = (Z.card : ℝ) * δ + (x / 2 + Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal)) := by
          rw [hsum_zero_part, hsum_nonzero_part]
        _ ≤ x / 2 + (x / 2 + Finset.sum (NZ.erase e₀) (fun e ↦ (p e).toReal)) := by
          gcongr
        _ = 1 := by
          linarith [hsum_nonzero_split]
    · -- Only the chosen atom changes its cross-entropy contribution; zero-mass symbols stay silent.
      let f : E → ℝ := fun e ↦ -(p e).toReal * Real.logb 2 (q e)
      let g : E → ℝ := fun e ↦ -(p e).toReal * Real.logb 2 ((p e).toReal)
      have hzero_f : Finset.sum Z f = 0 := by
        calc
          Finset.sum Z f = Finset.sum Z (fun _ ↦ (0 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            have hp : p e = 0 := by simpa [Z] using he
            simp [f, q, hp]
          _ = 0 := by simp
      have hzero_g : Finset.sum Z g = 0 := by
        calc
          Finset.sum Z g = Finset.sum Z (fun _ ↦ (0 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            have hp : p e = 0 := by simpa [Z] using he
            simp [g, hp]
          _ = 0 := by simp
      have hsum_f_nonzero :
          Finset.sum NZ f = Finset.sum NZ g + x := by
        calc
          Finset.sum NZ f =
              (-x * Real.logb 2 (x / 2)) + Finset.sum (NZ.erase e₀) g := by
            calc
              Finset.sum NZ f =
                  Finset.sum NZ (fun e ↦ if e = e₀ then -x * Real.logb 2 (x / 2) else g e) := by
                apply Finset.sum_congr rfl
                intro e he
                have hp : p e ≠ 0 := by simpa [NZ] using he
                by_cases he : e = e₀
                · subst he
                  simp [f, g, q, he₀_ne_zero, x]
                · simp [f, g, q, hp, he, x]
              _ = (-x * Real.logb 2 (x / 2)) + Finset.sum (NZ.erase e₀) g := by
                have herase :
                    Finset.sum (NZ.erase e₀)
                        (fun e ↦ if e = e₀ then -x * Real.logb 2 (x / 2) else g e) =
                      Finset.sum (NZ.erase e₀) g := by
                  apply Finset.sum_congr rfl
                  intro e he
                  have he' : e ≠ e₀ := (Finset.mem_erase.mp he).1
                  simp [he']
                rw [← Finset.sum_erase_add NZ
                  (fun e ↦ if e = e₀ then -x * Real.logb 2 (x / 2) else g e) he₀_mem_NZ]
                rw [herase]
                simpa [add_comm, add_left_comm, add_assoc]
          _ = (-x * Real.logb 2 x + x) + Finset.sum (NZ.erase e₀) g := by
            rw [neg_mul_logb_half x he₀]
          _ = Finset.sum NZ g + x := by
            rw [← Finset.sum_erase_add NZ g he₀_mem_NZ]
            simp [g, x]
            ring
      have hsum_f_all : (∑ e : E, f e) = Finset.sum NZ f := by
        calc
          ∑ e : E, f e = Finset.sum Z f + Finset.sum NZ f := by
            symm
            simpa [Z, NZ, f] using
              (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0) f)
          _ = Finset.sum NZ f := by simp [hzero_f]
      have hsum_g_all : (∑ e : E, g e) = Finset.sum NZ g := by
        calc
          ∑ e : E, g e = Finset.sum Z g + Finset.sum NZ g := by
            symm
            simpa [Z, NZ, g] using
              (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0) g)
          _ = Finset.sum NZ g := by simp [hzero_g]
      have hcross_eq : -∑ e : E, (p e).toReal * Real.logb 2 (q e) = (binaryEntropy p).toReal + x := by
        have hsum_g_eq : ∑ e : E, g e = (binaryEntropy p).toReal := by
          simpa [g] using (binaryEntropy_toReal_eq_sum p).symm
        calc
          -∑ e : E, (p e).toReal * Real.logb 2 (q e) = ∑ e : E, f e := by simp [f]
          _ = Finset.sum NZ f := hsum_f_all
          _ = Finset.sum NZ g + x := hsum_f_nonzero
          _ = ∑ e : E, g e + x := by rw [← hsum_g_all]
          _ = (binaryEntropy p).toReal + x := by rw [hsum_g_eq]
      have hx_le_one : x ≤ 1 := by
        calc
          x = (p e₀).toReal := rfl
          _ ≤ ∑ e : E, (p e).toReal := by
            simpa using
              Finset.single_le_sum (fun e _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ e₀)
          _ = 1 := sum_toReal_pmf p
      linarith [hcross_eq, hx_le_one]

/-- Helper for Theorem 5.27: a strictly positive sub-probability on a finite alphabet yields
Shannon lengths satisfying both the Kraft inequality and the usual pointwise `+1` ceiling bound. -/
theorem exists_binary_lengths_of_subprobability [Fintype E] (q : E → ℝ)
    (hq_pos : ∀ e, 0 < q e) (hq_sum : ∑ e : E, q e ≤ 1) :
    ∃ ℓ : E → ℕ,
      (∀ e, ((1 / 2 : ℝ) ^ ℓ e) ≤ q e) ∧
      (∀ e, (ℓ e : ℝ) ≤ -Real.logb 2 (q e) + 1) ∧
      (∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) ≤ 1) := by
  let ℓ : E → ℕ := fun e ↦ ⌈-Real.logb 2 (q e)⌉₊
  have hpow_le : ∀ e, ((1 / 2 : ℝ) ^ ℓ e) ≤ q e := by
    -- The Shannon ceiling places the dyadic mass `2^{-ℓ(e)}` below `q(e)`.
    intro e
    have hq_le_one : q e ≤ 1 := by
      calc
        q e ≤ ∑ x : E, q x := by
          simpa using Finset.single_le_sum (fun x _ ↦ le_of_lt (hq_pos x)) (Finset.mem_univ e)
        _ ≤ 1 := hq_sum
    have hceil : -Real.logb 2 (q e) ≤ ℓ e := Nat.le_ceil _
    have hpow :
        (2 : ℝ) ^ (-(ℓ e : ℝ)) ≤ q e := by
      have hle_log : (-(ℓ e : ℝ)) ≤ Real.logb 2 (q e) := by
        linarith
      exact (Real.le_logb_iff_rpow_le one_lt_two (hq_pos e)).mp hle_log
    calc
      ((1 / 2 : ℝ) ^ ℓ e) = ((1 / 2 : ℝ) ^ (ℓ e : ℝ)) := by rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ (-(ℓ e : ℝ)) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
        rw [Real.inv_rpow (show 0 ≤ (2 : ℝ) by positivity), Real.rpow_neg (show 0 ≤ (2 : ℝ) by positivity)]
      _ ≤ q e := hpow
  have hbound : ∀ e, (ℓ e : ℝ) ≤ -Real.logb 2 (q e) + 1 := by
    -- The natural ceiling is always less than one above the real number it rounds.
    intro e
    have hnonneg : 0 ≤ -Real.logb 2 (q e) := by
      have hq_le_one : q e ≤ 1 := by
        calc
          q e ≤ ∑ x : E, q x := by
            simpa using Finset.single_le_sum (fun x _ ↦ le_of_lt (hq_pos x)) (Finset.mem_univ e)
          _ ≤ 1 := hq_sum
      have hlog_nonpos : Real.logb 2 (q e) ≤ 0 := by
        exact (Real.logb_le_iff_le_rpow one_lt_two (hq_pos e)).2 (by simpa)
      linarith
    exact (Nat.ceil_lt_add_one hnonneg).le
  have hkraft : ∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) ≤ 1 := by
    -- Summing the pointwise dyadic bounds yields the Kraft inequality.
    refine le_trans ?_ hq_sum
    exact Finset.sum_le_sum fun e _ ↦ hpow_le e
  exact ⟨ℓ, hpow_le, hbound, hkraft⟩

/-- Helper for Theorem 5.27: any finite family can be assigned a uniform binary tail depth whose
Kraft sum still fits inside a single binary subtree. -/
theorem exists_binary_tail_lengths {Z : Type*} [Fintype Z] :
    ∃ τ : Z → ℕ, ∑ z : Z, ((1 / 2 : ℝ) ^ τ z) ≤ 1 := by
  classical
  let n : ℕ := Fintype.card Z
  let τ : Z → ℕ := fun _ ↦ n
  have hcard_le_pow : n ≤ 2 ^ n := by
    exact n.lt_two_pow_self.le
  have hreal : (n : ℝ) * ((1 / 2 : ℝ) ^ n) ≤ 1 := by
    have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
    have hcard_le_pow_real : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast hcard_le_pow
    have hdiv : (n : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
      refine (div_le_iff₀ hpow_pos).2 ?_
      simpa using hcard_le_pow_real
    simpa [one_div, inv_pow, div_eq_mul_inv, τ, n]
      using hdiv
  refine ⟨τ, ?_⟩
  -- All zero-mass symbols receive the same deep tail, so the Kraft sum is just a constant count.
  calc
    ∑ z : Z, ((1 / 2 : ℝ) ^ τ z) = (Fintype.card Z : ℝ) * ((1 / 2 : ℝ) ^ n) := by
      simp [τ, n, Finset.mul_sum]
    _ ≤ 1 := hreal

/-- Helper for Theorem 5.27: the Shannon ceiling length attached to a source symbol. -/
private noncomputable def shannonLength (p : PMF E) (e : E) : ℕ :=
  if p e = 0 then 0 else ⌈-Real.logb 2 (p e).toReal⌉₊

/-- Helper for Theorem 5.27: on the support of `p`, the Shannon ceiling length satisfies the
usual pointwise `+1` bound. -/
private theorem shannonLength_le_entropy_term [Fintype E] (p : PMF E) (e : E) (hp : p e ≠ 0) :
    (shannonLength p e : ℝ) ≤ -Real.logb 2 (p e).toReal + 1 := by
  -- The Shannon ceiling differs from the ideal binary length by at most one bit.
  have hq_pos : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
  have hq_le_one : (p e).toReal ≤ 1 := by
    calc
      (p e).toReal ≤ ∑ x : E, (p x).toReal := by
        simpa using Finset.single_le_sum (fun x _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ e)
      _ = 1 := sum_toReal_pmf p
  have hlog_nonpos : Real.logb 2 (p e).toReal ≤ 0 := by
    exact (Real.logb_le_iff_le_rpow one_lt_two hq_pos).2 (by simpa)
  have hnonneg : 0 ≤ -Real.logb 2 (p e).toReal := by linarith
  simpa [shannonLength, hp] using (Nat.ceil_lt_add_one hnonneg).le

/-- Helper for Theorem 5.27: on the support of `p`, the Shannon ceiling length produces a dyadic
mass bounded above by `p`. -/
private theorem shannonMass_le_toReal [Fintype E] (p : PMF E) (e : E) (hp : p e ≠ 0) :
    ((1 / 2 : ℝ) ^ shannonLength p e) ≤ (p e).toReal := by
  -- Exponentiating the ceiling inequality gives the standard Shannon upper bound.
  have hq_pos : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
  have hceil : -Real.logb 2 (p e).toReal ≤ shannonLength p e := by
    simpa [shannonLength, hp] using (Nat.le_ceil (-Real.logb 2 (p e).toReal))
  have hpow :
      (2 : ℝ) ^ (-(shannonLength p e : ℝ)) ≤ (p e).toReal := by
    have hle_log : (-(shannonLength p e : ℝ)) ≤ Real.logb 2 (p e).toReal := by
      linarith
    exact (Real.le_logb_iff_rpow_le one_lt_two hq_pos).mp hle_log
  calc
    ((1 / 2 : ℝ) ^ shannonLength p e) = ((1 / 2 : ℝ) ^ (shannonLength p e : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ (-(shannonLength p e : ℝ)) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      rw [Real.inv_rpow (show 0 ≤ (2 : ℝ) by positivity)]
      rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) by positivity)]
    _ ≤ (p e).toReal := hpow

/-- Helper for Theorem 5.27: the real masses of `p` still sum to `1` after restricting to the
positive support. -/
private theorem sum_toReal_pmf_on_support [Fintype E] (p : PMF E) :
    (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal) = 1 := by
  -- The zero-mass symbols contribute nothing, so the support carries the full mass.
  have hsplit :
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal) +
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal = 1 := by
    calc
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal) +
            ∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal =
          ∑ e : E, (p e).toReal := by
        simpa using
          (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
            (fun e ↦ (p e).toReal))
      _ = 1 := sum_toReal_pmf p
  have hzero :
      ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hp : p e = 0 := by simpa using he
    simp [hp]
  linarith

/-- Helper for Theorem 5.27: if the Shannon dyadic masses on the support already saturate the
binary tree, then they agree termwise with the source masses. -/
theorem support_shannon_lengths_eq_p_of_kraft_eq_one [Fintype E] (p : PMF E)
    (hKraft :
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), ((1 / 2 : ℝ) ^ shannonLength p e)) = 1) :
    ∀ e, p e ≠ 0 → ((1 / 2 : ℝ) ^ shannonLength p e) = (p e).toReal := by
  -- Equality of the total sums forces equality of each nonnegative support deficit.
  intro e hp
  let NZ : Finset E := Finset.univ.filter fun x ↦ p x ≠ 0
  let d : E → ℝ := fun x ↦ (p x).toReal - ((1 / 2 : ℝ) ^ shannonLength p x)
  have hd_nonneg : ∀ x ∈ NZ, 0 ≤ d x := by
    intro x hx
    have hx' : p x ≠ 0 := by simpa [NZ] using hx
    exact sub_nonneg.mpr (shannonMass_le_toReal p x hx')
  have hsum_d : ∑ x ∈ NZ, d x = 0 := by
    calc
      ∑ x ∈ NZ, d x =
          (∑ x ∈ NZ, (p x).toReal) - ∑ x ∈ NZ, ((1 / 2 : ℝ) ^ shannonLength p x) := by
        simp [NZ, d, Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [sum_toReal_pmf_on_support p, hKraft]
      _ = 0 := by ring
  have heq_zero :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x hx ↦ hd_nonneg x hx)).1 hsum_d e (by simpa [NZ] using hp)
  dsimp [d] at heq_zero
  linarith

/-- Helper for Theorem 5.27: removing the zero-mass symbols does not change the finite entropy
sum. -/
private theorem binaryEntropy_toReal_eq_support_sum [Fintype E] (p : PMF E) :
    (binaryEntropy p).toReal =
      -∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal * Real.logb 2 (p e).toReal := by
  let Z : Finset E := Finset.univ.filter fun e ↦ p e = 0
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  let f : E → ℝ := fun e ↦ (p e).toReal * Real.logb 2 (p e).toReal
  have hzero : ∑ e ∈ Z, f e = 0 := by
    -- Zero-mass terms vanish because the multiplicative factor `(p e).toReal` is already zero.
    apply Finset.sum_eq_zero
    intro e he
    have hp : p e = 0 := by simpa [Z] using he
    simp [f, hp]
  have hsplit : ∑ e : E, f e = (∑ e ∈ Z, f e) + ∑ e ∈ NZ, f e := by
    -- Split the full finite entropy sum into the zero-mass and positive-support parts.
    symm
    simpa [Z, NZ, f] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0) f)
  have hsupport : ∑ e : E, f e = ∑ e ∈ NZ, f e := by
    rw [hsplit, hzero, zero_add]
  -- Replace the full entropy sum by the support-restricted one.
  rw [binaryEntropy_toReal_eq_sum p, hsupport]

/-- Helper for Theorem 5.27: the Shannon support lengths already satisfy the standard `H + 1`
expected-length bound. -/
private theorem shannon_support_expectedLength_le_binaryEntropy_add_one [Fintype E] (p : PMF E) :
    (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal * (shannonLength p e : ℝ)) ≤
      (binaryEntropy p).toReal + 1 := by
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  -- Apply the pointwise Shannon ceiling estimate on the positive support and sum the result.
  calc
    ∑ e ∈ NZ, (p e).toReal * (shannonLength p e : ℝ) ≤
        ∑ e ∈ NZ, (-((p e).toReal * Real.logb 2 (p e).toReal) + (p e).toReal) := by
      refine Finset.sum_le_sum ?_
      intro e he
      have hp : p e ≠ 0 := by simpa [NZ] using he
      have hmul :
          (p e).toReal * (shannonLength p e : ℝ) ≤
            (p e).toReal * (-Real.logb 2 (p e).toReal + 1) := by
        exact mul_le_mul_of_nonneg_left (shannonLength_le_entropy_term p e hp) ENNReal.toReal_nonneg
      nlinarith
    _ = (-∑ e ∈ NZ, (p e).toReal * Real.logb 2 (p e).toReal) +
          ∑ e ∈ NZ, (p e).toReal := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_neg_distrib]
    _ = (binaryEntropy p).toReal + 1 := by
      rw [binaryEntropy_toReal_eq_support_sum p, sum_toReal_pmf_on_support p]

/-- Helper for Theorem 5.27: when the support Shannon Kraft sum saturates the binary tree, the
support Shannon expected length is exactly the binary entropy. -/
private theorem shannon_support_expectedLength_eq_binaryEntropy_of_kraft_eq_one [Fintype E]
    (p : PMF E)
    (hKraft :
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), ((1 / 2 : ℝ) ^ shannonLength p e)) = 1) :
    (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0), (p e).toReal * (shannonLength p e : ℝ)) =
      (binaryEntropy p).toReal := by
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  have hmass := support_shannon_lengths_eq_p_of_kraft_eq_one p hKraft
  -- Rewrite each support term using the exact dyadic identity supplied by the saturated Kraft sum.
  calc
    ∑ e ∈ NZ, (p e).toReal * (shannonLength p e : ℝ) =
        ∑ e ∈ NZ, -((p e).toReal * Real.logb 2 (p e).toReal) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      have hp : p e ≠ 0 := by simpa [NZ] using he
      have hlog :
          Real.logb 2 (p e).toReal = -(shannonLength p e : ℝ) := by
        rw [← hmass e hp, Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
        ring
      rw [hlog]
      ring
    _ = (binaryEntropy p).toReal := by
      calc
        ∑ e ∈ NZ, -((p e).toReal * Real.logb 2 (p e).toReal) =
            -∑ e ∈ NZ, (p e).toReal * Real.logb 2 (p e).toReal := by
          rw [← Finset.sum_neg_distrib]
        _ = (binaryEntropy p).toReal := by
          exact (binaryEntropy_toReal_eq_support_sum p).symm

/-- Helper for Theorem 5.27: there is a full binary length family whose Kraft sum is at most `1`
and whose `p`-expected length is at most the binary entropy plus one bit. -/
theorem exists_binary_lengths_expectedLength_le_binaryEntropy_add_one [Fintype E] (p : PMF E) :
    ∃ ℓ : E → ℕ,
      (∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) ≤ 1) ∧
      (∑ e : E, (p e).toReal * (ℓ e : ℝ) ≤ (binaryEntropy p).toReal + 1) := by
  classical
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  let Z0 := {e : E // p e = 0}
  let m : E → ℕ := shannonLength p
  let K : ℝ := ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ m e)
  have hK_le : K ≤ 1 := by
    -- The Shannon support masses are pointwise bounded by `p`, so their sum is at most `1`.
    calc
      K = ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ m e) := rfl
      _ ≤ ∑ e ∈ NZ, (p e).toReal := by
        refine Finset.sum_le_sum ?_
        intro e he
        have hp : p e ≠ 0 := by simpa [NZ] using he
        simpa [m] using shannonMass_le_toReal p e hp
      _ = 1 := sum_toReal_pmf_on_support p
  have htail : ∃ τ : Z0 → ℕ, ∑ z : Z0, ((1 / 2 : ℝ) ^ τ z) ≤ 1 := exists_binary_tail_lengths
  rcases htail with ⟨τ, hτ⟩
  rcases lt_or_eq_of_le hK_le with hKlt | hKeq
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, ((1 / 2 : ℝ) ^ k) < 1 - K := by
      -- Strict slack in the support Kraft sum leaves room for a deep zero-mass tail.
      exact exists_pow_lt_of_lt_one (sub_pos.mpr hKlt) (by norm_num : ((1 / 2 : ℝ) < 1))
    let ℓ : E → ℕ := fun e ↦
      if hp : p e = 0 then k + τ ⟨e, hp⟩ else m e
    refine ⟨ℓ, ?_, ?_⟩
    · have hzero_kraft :
          (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e)) ≤
            ((1 / 2 : ℝ) ^ k) := by
        -- Shift the generic zero-tail family to depth `k`; its Kraft mass scales by `2^{-k}`.
        calc
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e) =
              ∑ z ∈ Finset.subtype (fun e ↦ p e = 0) Finset.univ, ((1 / 2 : ℝ) ^ (k + τ z)) := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            apply Finset.sum_congr rfl
            intro z hz
            simp [ℓ, z.2]
          _ = ∑ z : Z0, ((1 / 2 : ℝ) ^ (k + τ z)) := by
            simp [Z0]
          _ = ((1 / 2 : ℝ) ^ k) * ∑ z : Z0, ((1 / 2 : ℝ) ^ τ z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            rw [pow_add]
          _ ≤ ((1 / 2 : ℝ) ^ k) * 1 := by
            gcongr
          _ = ((1 / 2 : ℝ) ^ k) := by ring
      have hsupport_kraft :
          ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) = K := by
        -- On the positive support, the length family is exactly the Shannon family.
        apply Finset.sum_congr rfl
        intro e he
        have hp : p e ≠ 0 := by simpa [NZ] using he
        simp [ℓ, hp, m, K]
      -- Split the Kraft sum into zero-mass and positive-support pieces.
      calc
        ∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e)) +
              ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ ((1 / 2 : ℝ) ^ ℓ e)))
        _ ≤ ((1 / 2 : ℝ) ^ k) + K := by
          have hsupport_kraft_le : ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) ≤ K := by
            rw [hsupport_kraft]
          linarith
        _ ≤ 1 := by
          linarith
    · have hzero_exp :
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal * (ℓ e : ℝ) = 0 := by
        -- Zero-mass symbols contribute nothing to the expected length.
        apply Finset.sum_eq_zero
        intro e he
        have hp : p e = 0 := by simpa using he
        simp [hp]
      have hsupport_exp :
          ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) =
            ∑ e ∈ NZ, (p e).toReal * (m e : ℝ) := by
        -- The support lengths are unchanged in the slack case.
        apply Finset.sum_congr rfl
        intro e he
        have hp : p e ≠ 0 := by simpa [NZ] using he
        simp [ℓ, hp, m]
      -- The zero part vanishes, so the expected-length bound comes entirely from the support.
      calc
        ∑ e : E, (p e).toReal * (ℓ e : ℝ) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal * (ℓ e : ℝ)) +
              ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ (p e).toReal * (ℓ e : ℝ)))
        _ = ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by rw [hzero_exp, zero_add]
        _ = ∑ e ∈ NZ, (p e).toReal * (m e : ℝ) := hsupport_exp
        _ ≤ (binaryEntropy p).toReal + 1 := shannon_support_expectedLength_le_binaryEntropy_add_one p
  · have hpos_atom : ∃ e₀ : E, p e₀ ≠ 0 := by
      -- A probability measure with total mass `1` must have a positive-support atom.
      by_contra hnone
      push Not at hnone
      have hsum_zero : (∑ e : E, (p e).toReal) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        simp [hnone e]
      rw [sum_toReal_pmf p] at hsum_zero
      norm_num at hsum_zero
    rcases hpos_atom with ⟨e₀, he₀⟩
    let ℓ : E → ℕ := fun e ↦
      if hp : p e = 0 then m e₀ + 1 + τ ⟨e, hp⟩ else if e = e₀ then m e + 1 else m e
    refine ⟨ℓ, ?_, ?_⟩
    · have hzero_kraft :
          (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e)) ≤
            ((1 / 2 : ℝ) ^ (m e₀ + 1)) := by
        -- The zero-mass tail sits inside the sibling subtree freed at depth `m e₀ + 1`.
        calc
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e) =
              ∑ z ∈ Finset.subtype (fun e ↦ p e = 0) Finset.univ,
                ((1 / 2 : ℝ) ^ (m e₀ + 1 + τ z)) := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            apply Finset.sum_congr rfl
            intro z hz
            simp [ℓ, z.2]
          _ = ∑ z : Z0, ((1 / 2 : ℝ) ^ (m e₀ + 1 + τ z)) := by
            simp [Z0]
          _ = ((1 / 2 : ℝ) ^ (m e₀ + 1)) * ∑ z : Z0, ((1 / 2 : ℝ) ^ τ z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            rw [pow_add]
          _ ≤ ((1 / 2 : ℝ) ^ (m e₀ + 1)) * 1 := by
            gcongr
          _ = ((1 / 2 : ℝ) ^ (m e₀ + 1)) := by ring
      have he₀_mem_NZ : e₀ ∈ NZ := by simp [NZ, he₀]
      have hsupport_kraft :
          ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) =
            K - ((1 / 2 : ℝ) ^ m e₀) + ((1 / 2 : ℝ) ^ (m e₀ + 1)) := by
        -- Lengthening one support atom by one bit removes half of its original cylinder.
        calc
          ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) =
              ((1 / 2 : ℝ) ^ ℓ e₀) + ∑ e ∈ NZ.erase e₀, ((1 / 2 : ℝ) ^ ℓ e) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_erase_add NZ (fun e ↦ ((1 / 2 : ℝ) ^ ℓ e)) he₀_mem_NZ).symm
          _ = ((1 / 2 : ℝ) ^ (m e₀ + 1)) + ∑ e ∈ NZ.erase e₀, ((1 / 2 : ℝ) ^ m e) := by
            congr 1
            · simp [ℓ, he₀]
            · apply Finset.sum_congr rfl
              intro e he
              have hp : p e ≠ 0 := by
                simpa [NZ] using (Finset.mem_of_mem_erase he)
              have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
              simp [ℓ, hp, hne, m]
          _ = K - ((1 / 2 : ℝ) ^ m e₀) + ((1 / 2 : ℝ) ^ (m e₀ + 1)) := by
            have hKsplit :
                K = ((1 / 2 : ℝ) ^ m e₀) + ∑ e ∈ NZ.erase e₀, ((1 / 2 : ℝ) ^ m e) := by
              rw [show K = ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ m e) by rfl]
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add NZ (fun e ↦ ((1 / 2 : ℝ) ^ m e)) he₀_mem_NZ).symm
            linarith
      -- The freed sibling subtree has exactly the same Kraft mass as the lengthened half-cylinder.
      calc
        ∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / 2 : ℝ) ^ ℓ e)) +
              ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ ((1 / 2 : ℝ) ^ ℓ e)))
        _ ≤ ((1 / 2 : ℝ) ^ (m e₀ + 1)) +
              (K - ((1 / 2 : ℝ) ^ m e₀) + ((1 / 2 : ℝ) ^ (m e₀ + 1))) := by
          have hsupport_kraft_le :
              ∑ e ∈ NZ, ((1 / 2 : ℝ) ^ ℓ e) ≤
                K - ((1 / 2 : ℝ) ^ m e₀) + ((1 / 2 : ℝ) ^ (m e₀ + 1)) := by
            rw [hsupport_kraft]
          linarith
        _ = K := by
          rw [pow_succ]
          ring
        _ = 1 := hKeq
    · have hzero_exp :
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal * (ℓ e : ℝ) = 0 := by
        -- The zero-mass symbols still make no contribution after being moved into the tail.
        apply Finset.sum_eq_zero
        intro e he
        have hp : p e = 0 := by simpa using he
        simp [hp]
      have he₀_mem_NZ : e₀ ∈ NZ := by simp [NZ, he₀]
      have hsupport_exp :
          ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) =
            (∑ e ∈ NZ, (p e).toReal * (m e : ℝ)) + (p e₀).toReal := by
        -- The only change on the support is the one extra bit assigned to `e₀`.
        calc
          ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) =
              (p e₀).toReal * (ℓ e₀ : ℝ) + ∑ e ∈ NZ.erase e₀, (p e).toReal * (ℓ e : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_erase_add NZ (fun e ↦ (p e).toReal * (ℓ e : ℝ)) he₀_mem_NZ).symm
          _ = (p e₀).toReal * ((m e₀ : ℝ) + 1) +
                ∑ e ∈ NZ.erase e₀, (p e).toReal * (m e : ℝ) := by
            congr 1
            · simp [ℓ, he₀]
            · apply Finset.sum_congr rfl
              intro e he
              have hp : p e ≠ 0 := by
                simpa [NZ] using (Finset.mem_of_mem_erase he)
              have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
              simp [ℓ, hp, hne, m]
          _ = ((p e₀).toReal * (m e₀ : ℝ) + (p e₀).toReal) +
                ∑ e ∈ NZ.erase e₀, (p e).toReal * (m e : ℝ) := by
            ring_nf
          _ = (∑ e ∈ NZ, (p e).toReal * (m e : ℝ)) + (p e₀).toReal := by
            have hsum :
                ∑ e ∈ NZ, (p e).toReal * (m e : ℝ) =
                  (p e₀).toReal * (m e₀ : ℝ) + ∑ e ∈ NZ.erase e₀, (p e).toReal * (m e : ℝ) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add NZ (fun e ↦ (p e).toReal * (m e : ℝ)) he₀_mem_NZ).symm
            rw [hsum]
            ring
      have he₀_le_one : (p e₀).toReal ≤ 1 := by
        calc
          (p e₀).toReal ≤ ∑ e : E, (p e).toReal := by
            simpa using
              Finset.single_le_sum (fun e _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ e₀)
          _ = 1 := sum_toReal_pmf p
      -- The saturated Shannon support already has entropy cost exactly `H`; only one extra bit remains.
      calc
        ∑ e : E, (p e).toReal * (ℓ e : ℝ) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal * (ℓ e : ℝ)) +
              ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ (p e).toReal * (ℓ e : ℝ)))
        _ = ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by rw [hzero_exp, zero_add]
        _ = (∑ e ∈ NZ, (p e).toReal * (m e : ℝ)) + (p e₀).toReal := hsupport_exp
        _ = (binaryEntropy p).toReal + (p e₀).toReal := by
          rw [shannon_support_expectedLength_eq_binaryEntropy_of_kraft_eq_one p hKeq]
        _ ≤ (binaryEntropy p).toReal + 1 := by gcongr

/-- Helper for Theorem 5.27: `bitString n x` is the fixed-length big-endian binary expansion of
`x`, truncated to `n` bits. -/
private def bitString (n x : ℕ) : List Bool :=
  List.ofFn fun i : Fin n ↦ x.testBit (n - 1 - i)

/-- Helper for Theorem 5.27: `bitString n x` always has length `n`. -/
private theorem bitString_length (n x : ℕ) : (bitString n x).length = n := by
  simp [bitString]

/-- Helper for Theorem 5.27: splitting a fixed-length big-endian word into a high-bit prefix and a
low-bit suffix corresponds to shifting right by the suffix length. -/
private theorem bitString_add (n m x : ℕ) :
    bitString (n + m) x = bitString n (x >>> m) ++ bitString m x := by
  -- Rewrite the `n + m` bits as the first `n` high bits followed by the last `m` low bits.
  unfold bitString
  rw [List.ofFn_add]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      have hi : i < n := by simpa using hi₂
      have hidx : n + m - 1 - i = m + (n - 1 - i) := by omega
      simp [List.getElem_ofFn, Nat.testBit_shiftRight, hidx]
  · apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      have hi : i < m := by simpa using hi₂
      have hidx : n + m - 1 - (n + i) = m - 1 - i := by omega
      simp [List.getElem_ofFn, hidx]

/-- Helper for Theorem 5.27: `decodeBitString n l` reads the first `n` bits of `l` as a
big-endian binary number. -/
private def decodeBitString (n : ℕ) (l : List Bool) : ℕ :=
  Nat.ofBits fun i : Fin n ↦ (l[n - 1 - i]? ).getD false

/-- Helper for Theorem 5.27: decoding the fixed-length binary expansion recovers the represented
number modulo `2 ^ n`. -/
private theorem decodeBitString_bitString (n x : ℕ) :
    decodeBitString n (bitString n x) = x % 2 ^ n := by
  -- Reversing the big-endian indexing recovers the usual little-endian `Nat.ofBits` input.
  unfold decodeBitString bitString
  have hbits :
      (fun i : Fin n ↦ ((List.ofFn fun j : Fin n ↦ x.testBit (n - 1 - j))[n - 1 - i]? ).getD false) =
        fun i : Fin n ↦ x.testBit i := by
    funext i
    have hi : n - 1 - i < n := by omega
    rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_ofFn]
    have hidx : n - 1 - (n - 1 - ↑i) = ↑i := by omega
    simp [hidx]
  rw [hbits]
  simpa using (Nat.ofBits_testBit x n)

/-- Helper for Theorem 5.27: the fixed-length big-endian representation is injective on numbers
strictly below `2 ^ n`. -/
private theorem bitString_injective {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (hxy : bitString n x = bitString n y) : x = y := by
  -- Decode both equal bitstrings back to naturals and use the size bounds to remove the modulus.
  have hdecode := congrArg (decodeBitString n) hxy
  rw [decodeBitString_bitString, decodeBitString_bitString, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] at hdecode
  exact hdecode

/-- Helper for Theorem 5.27: a finite family of binary lengths satisfying Kraft's inequality can
be realized by a binary prefix code with exactly those codeword lengths. -/
theorem exists_prefixCode_of_binary_lengths [Fintype E] (ℓ : E → ℕ)
    (hKraft : ∑ e : E, ((1 / 2 : ℝ) ^ ℓ e) ≤ 1) :
    ∃ C : PrefixCode Bool E, ∀ e, (C.encode e).length = ℓ e := by
  classical
  -- Route correction: realize the Kraft-admissible lengths by aligned dyadic blocks at a common
  -- depth, then encode each block by the fixed-length binary name of its left endpoint.
  let N : ℕ := Finset.univ.sup ℓ
  let index : E → Fin (Fintype.card E) := Fintype.equivFin E
  let precedes : E → E → Prop := fun e₁ e₂ ↦
    ℓ e₁ < ℓ e₂ ∨ (ℓ e₁ = ℓ e₂ ∧ index e₁ < index e₂)
  let predecessors : E → Finset E := fun e ↦ Finset.univ.filter fun e' ↦ precedes e' e
  let blockWidth : E → ℕ := fun e ↦ 2 ^ (N - ℓ e)
  let blockIndex : E → ℕ := fun e ↦ Finset.sum (predecessors e) fun a ↦ 2 ^ (ℓ e - ℓ a)
  let blockStart : E → ℕ := fun e ↦ blockIndex e * blockWidth e
  let totalWidth : ℕ := ∑ e : E, blockWidth e
  have hlength_le : ∀ e : E, ℓ e ≤ N := by
    intro e
    exact Finset.le_sup (Finset.mem_univ e)
  have hprecedes_irrefl : ∀ e : E, ¬ precedes e e := by
    intro e he
    rcases he with hlt | ⟨heq, hlt⟩
    · exact lt_irrefl _ hlt
    · exact lt_irrefl _ hlt
  have hprecedes_trans : ∀ {e₁ e₂ e₃ : E}, precedes e₁ e₂ → precedes e₂ e₃ → precedes e₁ e₃ := by
    intro e₁ e₂ e₃ h₁₂ h₂₃
    rcases h₁₂ with h₁₂ | ⟨h₁₂, hidx₁₂⟩
    · rcases h₂₃ with h₂₃ | ⟨h₂₃, _⟩
      · exact Or.inl (lt_trans h₁₂ h₂₃)
      · exact Or.inl (h₁₂.trans_le h₂₃.le)
    · rcases h₂₃ with h₂₃ | ⟨h₂₃, hidx₂₃⟩
      · exact Or.inl (h₁₂.le.trans_lt h₂₃)
      · exact Or.inr ⟨h₁₂.trans h₂₃, lt_trans hidx₁₂ hidx₂₃⟩
  have hprecedes_total : ∀ {e₁ e₂ : E}, e₁ ≠ e₂ → precedes e₁ e₂ ∨ precedes e₂ e₁ := by
    intro e₁ e₂ hne
    by_cases hlt : ℓ e₁ < ℓ e₂
    · exact Or.inl (Or.inl hlt)
    · by_cases hgt : ℓ e₂ < ℓ e₁
      · exact Or.inr (Or.inl hgt)
      · have hlen : ℓ e₁ = ℓ e₂ := by
          exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
        have hidx_ne : index e₁ ≠ index e₂ := by
          intro hidx
          exact hne ((Fintype.equivFin E).injective hidx)
        exact (lt_or_gt_of_ne hidx_ne).elim
          (fun hidx ↦ Or.inl (Or.inr ⟨hlen, hidx⟩))
          (fun hidx ↦ Or.inr (Or.inr ⟨hlen.symm, hidx⟩))
  have hblockStart_sum :
      ∀ e : E, blockStart e = Finset.sum (predecessors e) fun e' ↦ blockWidth e' := by
    intro e
    -- Each predecessor contributes a full dyadic block of width `2 ^ (N - ℓ e')`.
    simp [blockStart, blockIndex, blockWidth]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e' he'
    have hpred : precedes e' e := (Finset.mem_filter.mp he').2
    have hle : ℓ e' ≤ ℓ e := by
      rcases hpred with hlt | ⟨heq, _⟩
      · exact hlt.le
      · exact heq.le
    calc
      2 ^ (ℓ e - ℓ e') * 2 ^ (N - ℓ e) = 2 ^ ((ℓ e - ℓ e') + (N - ℓ e)) := by
        rw [← Nat.pow_add]
      _ = 2 ^ (N - ℓ e') := by
        have hN : ℓ e ≤ N := hlength_le e
        congr
        omega
      _ = blockWidth e' := by
        simp [blockWidth]
  have htotalWidth_nat : totalWidth ≤ 2 ^ N := by
    -- Multiply the Kraft inequality by the common depth `2 ^ N`.
    have hterm : ∀ e : E, ((1 / 2 : ℝ) ^ ℓ e) * (2 : ℝ) ^ N = (blockWidth e : ℝ) := by
      intro e
      have hle : ℓ e ≤ N := hlength_le e
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      calc
        ((1 / 2 : ℝ) ^ ℓ e) * (2 : ℝ) ^ N = (1 / (2 : ℝ) ^ ℓ e) * (2 : ℝ) ^ N := by
          rw [one_div_pow]
        _ = (((2 : ℝ) ^ ℓ e)⁻¹) * (2 : ℝ) ^ N := by
          simp [one_div]
        _ = (2 : ℝ) ^ (N - ℓ e) := by
          rw [mul_comm, ← pow_sub₀ (2 : ℝ) htwo hle]
        _ = (blockWidth e : ℝ) := by
          simp [blockWidth]
    have hscaled := mul_le_mul_of_nonneg_right hKraft (by positivity : 0 ≤ (2 : ℝ) ^ N)
    have hreal : (totalWidth : ℝ) ≤ (2 : ℝ) ^ N := by
      calc
        (totalWidth : ℝ) = ∑ e : E, (blockWidth e : ℝ) := by
          simp [totalWidth]
        _ = ∑ e : E, (((1 / 2 : ℝ) ^ ℓ e) * (2 : ℝ) ^ N) := by
          apply Finset.sum_congr rfl
          intro e he
          exact (hterm e).symm
        _ = (∑ e : E, ((1 / 2 : ℝ) ^ ℓ e)) * (2 : ℝ) ^ N := by
          rw [Finset.sum_mul]
        _ ≤ 1 * (2 : ℝ) ^ N := hscaled
        _ = (2 : ℝ) ^ N := by ring
    exact_mod_cast hreal
  have hstart_step : ∀ {e₁ e₂ : E}, precedes e₁ e₂ →
      blockStart e₁ + blockWidth e₁ ≤ blockStart e₂ := by
    intro e₁ e₂ h₁₂
    -- Earlier blocks and the current block sit inside the predecessor family of any later symbol.
    have hsubset : insert e₁ (predecessors e₁) ⊆ predecessors e₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁₂⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprecedes_trans (Finset.mem_filter.mp hx).2 h₁₂⟩
    have hsum_le :
        Finset.sum (insert e₁ (predecessors e₁)) (fun x ↦ blockWidth x) ≤
          Finset.sum (predecessors e₂) (fun x ↦ blockWidth x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ ↦ Nat.zero_le _
    have hnot_mem : e₁ ∉ predecessors e₁ := by
      intro he
      exact hprecedes_irrefl e₁ (Finset.mem_filter.mp he).2
    calc
      blockStart e₁ + blockWidth e₁ =
          Finset.sum (insert e₁ (predecessors e₁)) fun x ↦ blockWidth x := by
        rw [Finset.sum_insert hnot_mem, add_comm, hblockStart_sum]
      _ ≤ Finset.sum (predecessors e₂) fun x ↦ blockWidth x := hsum_le
      _ = blockStart e₂ := (hblockStart_sum e₂).symm
  have hstartSucc_le_total : ∀ e : E, blockStart e + blockWidth e ≤ totalWidth := by
    intro e
    -- The current block and all earlier blocks are part of the full dyadic partition.
    have hsubset : insert e (predecessors e) ⊆ Finset.univ := by
      intro x hx
      simp
    have hsum_le :
        Finset.sum (insert e (predecessors e)) (fun x ↦ blockWidth x) ≤
          Finset.sum Finset.univ (fun x ↦ blockWidth x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ ↦ Nat.zero_le _
    have hnot_mem : e ∉ predecessors e := by
      intro he
      exact hprecedes_irrefl e (Finset.mem_filter.mp he).2
    calc
      blockStart e + blockWidth e =
          Finset.sum (insert e (predecessors e)) fun x ↦ blockWidth x := by
        rw [Finset.sum_insert hnot_mem, add_comm, hblockStart_sum]
      _ ≤ Finset.sum Finset.univ fun x ↦ blockWidth x := hsum_le
      _ = totalWidth := by simp [totalWidth]
  have hblockIndex_lt : ∀ e : E, blockIndex e < 2 ^ ℓ e := by
    intro e
    -- The aligned dyadic block starting at `blockStart e` must fit into the depth-`N` tree.
    have hfit : blockStart e + blockWidth e ≤ 2 ^ N := le_trans (hstartSucc_le_total e) htotalWidth_nat
    have hrewrite : blockStart e + blockWidth e = (blockIndex e + 1) * blockWidth e := by
      simp [blockStart, blockWidth, Nat.succ_mul]
    have hpow : 2 ^ N = (2 ^ ℓ e) * blockWidth e := by
      simp [blockWidth, ← Nat.pow_add]
      have hle : ℓ e ≤ N := hlength_le e
      omega
    have hle :
        blockIndex e + 1 ≤ 2 ^ ℓ e := by
      apply Nat.le_of_mul_le_mul_right
      · simpa [hrewrite, hpow]
          using hfit
      · simp [blockWidth]
    exact Nat.lt_of_succ_le hle
  let encode : E → List Bool := fun e ↦ bitString (ℓ e) (blockIndex e)
  have hencode_length : ∀ e : E, (encode e).length = ℓ e := by
    intro e
    simp [encode, bitString_length]
  have hprefix_forces_interval : ∀ {e₁ e₂ : E}, encode e₁ <+: encode e₂ →
      blockStart e₂ < blockStart e₁ + blockWidth e₁ := by
    intro e₁ e₂ hprefix
    rcases hprefix with ⟨tail, htail⟩
    have hlen_le : ℓ e₁ ≤ ℓ e₂ := by
      have hlen_eq := congrArg List.length htail
      rw [List.length_append, hencode_length e₁, hencode_length e₂] at hlen_eq
      omega
    let d : ℕ := ℓ e₂ - ℓ e₁
    have hd : ℓ e₂ = ℓ e₁ + d := by
      simp [d, Nat.add_sub_of_le hlen_le]
    have htake :
        bitString (ℓ e₁) (blockIndex e₁) = bitString (ℓ e₁) (blockIndex e₂ >>> d) := by
      -- Taking the first `ℓ e₁` bits of the later codeword recovers the earlier codeword.
      have htail' : bitString (ℓ e₁) (blockIndex e₁) ++ tail = bitString (ℓ e₂) (blockIndex e₂) := by
        simpa [encode] using htail
      rw [hd, bitString_add] at htail'
      have htake' := congrArg (List.take (ℓ e₁)) htail'
      simpa [bitString_length] using htake'
    have hshift_lt : blockIndex e₂ >>> d < 2 ^ ℓ e₁ := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos d)]
      have hpow : 2 ^ ℓ e₂ = 2 ^ ℓ e₁ * 2 ^ d := by
        rw [hd, Nat.pow_add]
      exact hpow ▸ hblockIndex_lt e₂
    have hquot : blockIndex e₁ = blockIndex e₂ >>> d :=
      bitString_injective (hblockIndex_lt e₁) hshift_lt htake
    have hquot' : blockIndex e₁ = blockIndex e₂ / 2 ^ d := by
      simpa [Nat.shiftRight_eq_div_pow] using hquot
    have hdiv_lt : blockIndex e₂ < (blockIndex e₁ + 1) * 2 ^ d := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos d)).mp
      rw [hquot']
      exact Nat.lt_succ_self _
    calc
      blockStart e₂ = blockIndex e₂ * 2 ^ (N - ℓ e₂) := by
        simp [blockStart, blockWidth]
      _ < ((blockIndex e₁ + 1) * 2 ^ d) * 2 ^ (N - ℓ e₂) := by
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hdiv_lt
      _ = (blockIndex e₁ + 1) * 2 ^ (N - ℓ e₁) := by
        rw [Nat.mul_assoc]
        have hle : ℓ e₂ ≤ N := hlength_le e₂
        congr 1
        rw [← Nat.pow_add]
        congr
        omega
      _ = blockStart e₁ + blockWidth e₁ := by
        simp [blockStart, blockWidth, Nat.succ_mul]
  have hprefix_free : Pairwise (fun e₁ e₂ ↦ ¬ (encode e₁ <+: encode e₂)) := by
    intro e₁ e₂ hne hprefix
    -- The aligned dyadic blocks are disjoint, so a later codeword cannot lie in an earlier
    -- codeword cylinder, and equal-length reverse-order collisions are excluded as well.
    have horder := hprecedes_total hne
    rcases horder with h₁₂ | h₂₁
    · exact (not_lt_of_ge (hstart_step h₁₂)) (hprefix_forces_interval hprefix)
    · rcases h₂₁ with hlt | ⟨hlen, hidx⟩
      · rcases hprefix with ⟨tail, htail⟩
        have hlen_le : ℓ e₁ ≤ ℓ e₂ := by
          have hlen_eq := congrArg List.length htail
          rw [List.length_append, hencode_length e₁, hencode_length e₂] at hlen_eq
          omega
        exact (not_lt_of_ge hlen_le) hlt
      · have hsameLength : ℓ e₁ = ℓ e₂ := hlen.symm
        have hprefix_eq : encode e₁ = encode e₂ := by
          rcases hprefix with ⟨tail, htail⟩
          have htail_nil : tail = [] := by
            have hlen_eq := congrArg List.length htail
            rw [List.length_append, hencode_length e₁, hencode_length e₂, hsameLength] at hlen_eq
            have htail_len : tail.length = 0 := by omega
            simpa [List.length_eq_zero_iff] using htail_len
          simpa [htail_nil] using htail
        have hindex_eq : blockIndex e₁ = blockIndex e₂ := by
          apply bitString_injective (n := ℓ e₁)
          · simpa using hblockIndex_lt e₁
          · simpa [hsameLength] using hblockIndex_lt e₂
          · simpa [encode, hsameLength] using hprefix_eq
        have hstart_eq : blockStart e₁ = blockStart e₂ := by
          simp [blockStart, blockWidth, hsameLength, hindex_eq]
        have hstrict : blockStart e₂ < blockStart e₁ := by
          have hpos : 0 < blockWidth e₂ := by simp [blockWidth]
          exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) (hstart_step (Or.inr ⟨hlen, hidx⟩))
        exact (lt_irrefl _) (hstart_eq ▸ hstrict)
  let C : PrefixCode Bool E := ⟨encode, hprefix_free⟩
  refine ⟨C, ?_⟩
  -- The codewords were built with the prescribed lengths by construction.
  exact hencode_length

-- Proof sketch: choose Shannon lengths `l(e) = ⌈-log₂ p_e⌉`, verify the Kraft inequality, and use
-- the standard construction of a binary prefix code with these lengths; the ceiling estimate gives
-- the extra `+ 1` in the expected-length bound.
/-- Theorem 5.27 (2): there exists a binary prefix code whose expected length is at most the binary
entropy plus `1`. -/
theorem exists_prefixCode_expectedLength_le_binaryEntropy_add_one [Fintype E]
    (p : PMF E) :
    ∃ C : PrefixCode Bool E, C.expectedLength p ≤ (binaryEntropy p).toReal + 1 := by
  -- Route correction: the entropy-side construction is now handled directly at the level of
  -- binary lengths, so the theorem reduces to realizing those lengths as an actual prefix code.
  rcases exists_binary_lengths_expectedLength_le_binaryEntropy_add_one p with ⟨ℓ, hKraft, hExp⟩
  rcases exists_prefixCode_of_binary_lengths ℓ hKraft with ⟨C, hlen⟩
  refine ⟨C, ?_⟩
  -- Rewrite the expected code length using the exact codeword-length realization.
  calc
    C.expectedLength p = ∑ e : E, (p e).toReal * (ℓ e : ℝ) := by
      rw [PrefixCode.expectedLength_def]
      apply Finset.sum_congr rfl
      intro e he
      rw [hlen e]
    _ ≤ (binaryEntropy p).toReal + 1 := hExp
