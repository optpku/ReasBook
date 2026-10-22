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

universe u

/-- A prefix code on an alphabet `E` with code alphabet `α` is an assignment of codewords such
that no codeword is a prefix of a different one. -/
structure PrefixCode (α : Type*) (E : Type u) where
  encode : E → List α
  prefix_free : Pairwise (fun e₁ e₂ ↦ ¬ (encode e₁ <+: encode e₂))

namespace PrefixCode

variable {α : Type*} {E : Type u}

/-- Prefix-freeness forces the encoding map of a prefix code to be injective. -/
theorem injective (C : PrefixCode α E) : Function.Injective C.encode := by
  intro e₁ e₂ hencode
  by_contra hne
  exact (C.prefix_free hne) (hencode ▸ by simp)

/-- The image of a prefix code is uniquely decodable as soon as no codeword is empty. -/
theorem uniquelyDecodable (C : PrefixCode α E) (hε : ∀ e, C.encode e ≠ []) :
    UniquelyDecodable (Set.range C.encode) := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ _ h₂ hflat
      cases L₂ with
      | nil => rfl
      | cons w₂ t₂ =>
          rcases h₂ w₂ (by simp) with ⟨e₂, rfl⟩
          simp [hε e₂] at hflat
  | cons w₁ t₁ ih =>
      intro L₂ h₁ h₂ hflat
      rcases h₁ w₁ (by simp) with ⟨e₁, rfl⟩
      cases L₂ with
      | nil =>
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

/-- The expected code length is the `p`-weighted sum of the codeword lengths. -/
@[simp] theorem expectedLength_def (C : PrefixCode α E) (p : PMF E) :
    C.expectedLength p = ∑ e : E, (p e).toReal * (C.encode e).length := rfl

end PrefixCode

/-- Helper for the base-`b` source-coding exercise: a natural base `b ≥ 2` gives a real
logarithmic base `> 1`. -/
private theorem nat_base_one_lt (b : ℕ) (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have h : (1 : ℕ) < b := lt_of_lt_of_le one_lt_two hb
  exact_mod_cast h

/-- The logarithmic base attached to a natural base `b ≥ 2`. -/
def nat_base (b : ℕ) (hb : 2 ≤ b) : LogBase :=
  ⟨b, by positivity, ne_of_gt (nat_base_one_lt b hb)⟩

variable {E : Type u}

/-- Helper for Exercise 5.3.5: if a prefix code over any alphabet contains the empty word, then
the source alphabet is subsingleton. -/
private theorem subsingleton_of_empty_codeword {α : Type*} (C : PrefixCode α E) {e₀ : E}
    (he₀ : C.encode e₀ = []) : Subsingleton E := by
  -- Any second symbol would have its codeword extending the empty word,
  -- contradicting prefix-freeness.
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  have hone : ∀ e : E, e = e₀ := by
    intro e
    by_contra hne
    have hempty : C.encode e₀ <+: C.encode e := by
      simp [he₀]
    exact (C.prefix_free (fun h ↦ hne h.symm)) hempty
  simp [hone e₁, hone e₂]

/-- Helper for Exercise 5.3.5: the Kraft sum of a `Fin b`-adic prefix code is at most `1`. -/
private theorem prefixCodeKraftSumLeOneFin [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (C : PrefixCode (Fin b) E) :
    ∑ e : E, ((1 / b : ℝ) ^ (C.encode e).length) ≤ 1 := by
  classical
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_two hb
  letI : Nonempty (Fin b) := ⟨⟨0, hb_pos⟩⟩
  by_cases hε : ∃ e, C.encode e = []
  · rcases hε with ⟨e₀, he₀⟩
    have hsub : Subsingleton E := subsingleton_of_empty_codeword C he₀
    letI : Subsingleton E := hsub
    letI : Unique E :=
      { default := e₀
        uniq := fun e ↦ Subsingleton.elim _ _ }
    have hdefault : C.encode default = [] := by simpa using he₀
    -- In the degenerate singleton case, the whole Kraft sum is the single empty-word contribution.
    simp [hdefault]
  · have hnonempty : ∀ e, C.encode e ≠ [] := by
      intro e he
      exact hε ⟨e, he⟩
    have hud :
        UniquelyDecodable
          ((Finset.image C.encode (Finset.univ : Finset E) : Finset (List (Fin b))) :
            Set (List (Fin b))) := by
      simpa using (C.uniquelyDecodable hnonempty)
    have hk :
        ∑ w ∈ Finset.image C.encode (Finset.univ : Finset E),
            (1 / (Fintype.card (Fin b) : ℝ)) ^ w.length ≤ 1 :=
      kraft_mcmillan_inequality hud
    -- Reindex the Kraft sum from distinct codewords back to the source alphabet.
    rw [Finset.sum_image C.injective.injOn] at hk
    simpa [Fintype.card_fin] using hk

/-- Helper for Exercise 5.3.5: on a finite alphabet, the real masses of a probability mass
function sum to `1`. -/
private theorem sumToRealPmf [Fintype E] (p : PMF E) :
    ∑ e : E, (p e).toReal = 1 := by
  -- Rewrite the finite sum as a `tsum` and use the standard `ENNReal.toReal` summation formula.
  have htsum :
      (∑' e : E, p e).toReal = ∑' e : E, (p e).toReal :=
    ENNReal.tsum_toReal_eq fun e ↦ p.apply_ne_top e
  rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
  simpa using htsum.symm

/-- Helper for Exercise 5.3.5: Jensen's inequality for `x ↦ x * log x`, written in the
Kullback-Leibler form `∑ p * log (p / w) ≥ 0`. -/
private theorem sumMulLogRatio_nonneg [Fintype E]
    (p : PMF E) (w : E → ℝ) (hw_sum : ∑ e : E, w e = 1) (hw_pos : ∀ e, 0 < w e) :
    0 ≤ ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) := by
  let φ : ℝ → ℝ := fun x ↦ x * Real.log x
  have hconv : ConvexOn ℝ (Set.Ici 0) φ := by
    simpa [φ] using Real.convexOn_mul_log
  have hmem : ∀ e : E, ((p e).toReal / w e) ∈ Set.Ici (0 : ℝ) := by
    intro e
    exact div_nonneg ENNReal.toReal_nonneg (le_of_lt (hw_pos e))
  have hnonneg : ∀ e : E, 0 ≤ w e := by
    intro e
    exact le_of_lt (hw_pos e)
  have hj :=
    ConvexOn.map_sum_le (t := Finset.univ) (w := w)
      (p := fun e ↦ (p e).toReal / w e) hconv (fun e _ ↦ hnonneg e) hw_sum (fun e _ ↦ hmem e)
  have hweighted : ∑ e : E, w e * ((p e).toReal / w e) = 1 := by
    calc
      ∑ e : E, w e * ((p e).toReal / w e) = ∑ e : E, (p e).toReal := by
        apply Finset.sum_congr rfl
        intro e he
        field_simp [ne_of_gt (hw_pos e)]
      _ = 1 := sumToRealPmf p
  have hkl :
      0 ≤ ∑ e : E, w e * (((p e).toReal / w e) * Real.log ((p e).toReal / w e)) := by
    have hj' :
        φ (∑ e : E, w e * ((p e).toReal / w e)) ≤
          ∑ e : E, w e * φ ((p e).toReal / w e) := by
      simpa [smul_eq_mul] using hj
    rw [hweighted] at hj'
    simpa [φ] using hj'
  have hrewrite :
      (∑ e : E, w e * (((p e).toReal / w e) * Real.log ((p e).toReal / w e))) =
        ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) := by
    apply Finset.sum_congr rfl
    intro e he
    field_simp [ne_of_gt (hw_pos e)]
  rwa [hrewrite] at hkl

/-- Helper for Exercise 5.3.5: the expected length of a `b`-adic prefix code is the weighted
negative logarithm of its Kraft weights. -/
private theorem natBaseExpectedLengthEqNegativeLogCodeweightSum [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (C : PrefixCode (Fin b) E) :
    C.expectedLength p =
      -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ)
        ((1 / b : ℝ) ^ (C.encode e).length) := by
  rw [PrefixCode.expectedLength_def]
  calc
    ∑ e : E, (p e).toReal * (C.encode e).length =
        ∑ e : E,
          -((p e).toReal * Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length)) := by
      apply Finset.sum_congr rfl
      intro e he
      have hself : Real.logb (nat_base b hb : ℝ) (b : ℝ) = 1 := by
        simpa using Real.logb_self_eq_one (nat_base_one_lt b hb)
      calc
        (p e).toReal * (C.encode e).length =
            -((p e).toReal * (-(C.encode e).length : ℝ)) := by
          ring
        _ = -((p e).toReal *
              Real.logb (nat_base b hb : ℝ) ((1 / b : ℝ) ^ (C.encode e).length)) := by
          rw [Real.logb_pow, one_div, Real.logb_inv, hself]
          ring
    _ = -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ)
          ((1 / b : ℝ) ^ (C.encode e).length) := by
      rw [← Finset.sum_neg_distrib]

-- Proof sketch: apply the same Kraft-inequality and cross-entropy argument as in the binary case,
-- replacing the binary weights `2 ^ (-length)` by the `b`-ary weights `b ^ (-length)` and the
-- logarithm base `2` by base `b`.
/-- Lower-bound half of Exercise 5.3.5: for a finite alphabet, the expected length of a prefix
code over the digit alphabet `Fin b` is
bounded below by the real value of the base-`b` entropy `H_b(p)` of the source law. -/
theorem entropy_in_nat_base_le_expected_length_of_b_adic_prefix_code [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (C : PrefixCode (Fin b) E) :
    (entropyInBase (nat_base b hb) p).toReal ≤ C.expectedLength p := by
  classical
  let r : E → ℝ := fun e ↦ ((1 / b : ℝ) ^ (C.encode e).length)
  let Q : ℝ := ∑ e : E, r e
  let w : E → ℝ := fun e ↦ r e / Q
  letI : Nonempty E := ⟨p.support_nonempty.some⟩
  have hr_pos : ∀ e : E, 0 < r e := by
    intro e
    have hbase_pos : 0 < (1 / b : ℝ) := by positivity
    simpa [r] using pow_pos hbase_pos (C.encode e).length
  have hQ_pos : 0 < Q := by
    let e₀ : E := Classical.choice inferInstance
    calc
      0 < r e₀ := hr_pos e₀
      _ ≤ ∑ e : E, r e := by
        simpa [Q] using
          Finset.single_le_sum (fun e _ ↦ le_of_lt (hr_pos e)) (Finset.mem_univ e₀)
  have hQ_le_one : Q ≤ 1 := by
    simpa [Q, r] using prefixCodeKraftSumLeOneFin b hb C
  have hw_sum : ∑ e : E, w e = 1 := by
    calc
      ∑ e : E, w e = (∑ e : E, r e) / Q := by
        simp [w, Q, Finset.sum_div]
      _ = 1 := by
        simp [Q, hQ_pos.ne']
  have hw_pos : ∀ e : E, 0 < w e := by
    intro e
    exact div_pos (hr_pos e) hQ_pos
  have hkl_nonneg :
      0 ≤ ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) :=
    sumMulLogRatio_nonneg p w hw_sum hw_pos
  have hratio :
      (∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e)) =
        ∑ e : E, (p e).toReal * Real.log (p e).toReal -
          ∑ e : E, (p e).toReal * Real.log (w e) := by
    calc
      ∑ e : E, (p e).toReal * Real.log ((p e).toReal / w e) =
          ∑ e : E,
            ((p e).toReal * Real.log (p e).toReal -
              (p e).toReal * Real.log (w e)) := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hp : p e = 0
        · simp [hp]
        · rw [Real.log_div (ENNReal.toReal_pos hp (p.apply_ne_top e)).ne' (ne_of_gt (hw_pos e))]
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
  have hentropy_le_w :
      -∑ e : E, (p e).toReal * Real.log (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.log (w e) := by
    rw [hratio] at hkl_nonneg
    linarith
  have hw_eq :
      (-∑ e : E, (p e).toReal * Real.log (w e)) =
        (-∑ e : E, (p e).toReal * Real.log (r e)) + Real.log Q := by
    calc
      -∑ e : E, (p e).toReal * Real.log (w e) =
          -∑ e : E, ((p e).toReal * Real.log (r e) - (p e).toReal * Real.log Q) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        rw [show w e = r e / Q by rfl, Real.log_div (ne_of_gt (hr_pos e)) (ne_of_gt hQ_pos)]
        ring
      _ = -((∑ e : E, (p e).toReal * Real.log (r e)) -
            ∑ e : E, (p e).toReal * Real.log Q) := by
        rw [Finset.sum_sub_distrib]
      _ = (-∑ e : E, (p e).toReal * Real.log (r e)) +
            ∑ e : E, (p e).toReal * Real.log Q := by
        ring
      _ = (-∑ e : E, (p e).toReal * Real.log (r e)) +
            Real.log Q * ∑ e : E, (p e).toReal := by
        congr 1
        calc
          ∑ e : E, (p e).toReal * Real.log Q = ∑ e : E, Real.log Q * (p e).toReal := by
            apply Finset.sum_congr rfl
            intro e he
            ring
          _ = Real.log Q * ∑ e : E, (p e).toReal := by
            rw [Finset.mul_sum]
      _ = (-∑ e : E, (p e).toReal * Real.log (r e)) + Real.log Q := by
        rw [sumToRealPmf p]
        ring
  have hlogQ_nonpos : Real.log Q ≤ 0 := by
    exact Real.log_nonpos hQ_pos.le hQ_le_one
  have hnat :
      -∑ e : E, (p e).toReal * Real.log (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.log (r e) := by
    rw [hw_eq] at hentropy_le_w
    linarith
  have hcoeff_pos : 0 < (Real.log (b : ℝ))⁻¹ := by
    exact inv_pos.mpr (Real.log_pos (nat_base_one_lt b hb))
  have hlogb :
      -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal ≤
        -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ) (r e) := by
    have hscaled := mul_le_mul_of_nonneg_left hnat (le_of_lt hcoeff_pos)
    simpa [Real.logb, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      using hscaled
  calc
    (entropyInBase (nat_base b hb) p).toReal =
        -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal := by
      exact entropyInBase_toReal_eq_sum (nat_base b hb) p
    _ ≤ -∑ e : E, (p e).toReal * Real.logb (nat_base b hb : ℝ) (r e) := hlogb
    _ = C.expectedLength p := by
      simpa [r] using (natBaseExpectedLengthEqNegativeLogCodeweightSum b hb p C).symm

/-- Helper for Exercise 5.3.5: a strictly positive sub-probability on a finite alphabet yields
base-`b` Shannon lengths satisfying both the Kraft inequality and the usual pointwise `+1`
ceiling bound. -/
private theorem existsNatBaseLengthsOfSubprobability [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (q : E → ℝ) (hq_pos : ∀ e, 0 < q e) (hq_sum : ∑ e : E, q e ≤ 1) :
    ∃ ℓ : E → ℕ,
      (∀ e, ((1 / b : ℝ) ^ ℓ e) ≤ q e) ∧
      (∀ e, (ℓ e : ℝ) ≤ -Real.logb (nat_base b hb : ℝ) (q e) + 1) ∧
      (∑ e : E, ((1 / b : ℝ) ^ ℓ e) ≤ 1) := by
  let ℓ : E → ℕ := fun e ↦ ⌈-Real.logb (nat_base b hb : ℝ) (q e)⌉₊
  have hpow_le : ∀ e, ((1 / b : ℝ) ^ ℓ e) ≤ q e := by
    -- The Shannon ceiling places the `b`-adic mass `b^{-ℓ(e)}` below `q(e)`.
    intro e
    have hq_le_one : q e ≤ 1 := by
      calc
        q e ≤ ∑ x : E, q x := by
          simpa using Finset.single_le_sum (fun x _ ↦ le_of_lt (hq_pos x)) (Finset.mem_univ e)
        _ ≤ 1 := hq_sum
    have hceil : -Real.logb (nat_base b hb : ℝ) (q e) ≤ ℓ e := Nat.le_ceil _
    have hpow :
        ((nat_base b hb : ℝ) ^ (-(ℓ e : ℝ))) ≤ q e := by
      have hle_log : (-(ℓ e : ℝ)) ≤ Real.logb (nat_base b hb : ℝ) (q e) := by
        linarith
      exact (Real.le_logb_iff_rpow_le (nat_base_one_lt b hb) (hq_pos e)).mp hle_log
    calc
      ((1 / b : ℝ) ^ ℓ e) = ((1 / b : ℝ) ^ (ℓ e : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (((nat_base b hb : ℝ)⁻¹) ^ (ℓ e : ℝ)) := by
        change ((1 / (b : ℝ)) ^ (ℓ e : ℝ)) = (((b : ℝ)⁻¹) ^ (ℓ e : ℝ))
        rw [one_div]
      _ = ((nat_base b hb : ℝ) ^ (-(ℓ e : ℝ))) := by
        exact (Real.rpow_neg_eq_inv_rpow (nat_base b hb : ℝ) (ℓ e : ℝ)).symm
      _ ≤ q e := hpow
  have hbound : ∀ e, (ℓ e : ℝ) ≤ -Real.logb (nat_base b hb : ℝ) (q e) + 1 := by
    -- The natural ceiling is always less than one above the real number it rounds.
    intro e
    have hnonneg : 0 ≤ -Real.logb (nat_base b hb : ℝ) (q e) := by
      have hq_le_one : q e ≤ 1 := by
        calc
          q e ≤ ∑ x : E, q x := by
            simpa using Finset.single_le_sum (fun x _ ↦ le_of_lt (hq_pos x)) (Finset.mem_univ e)
          _ ≤ 1 := hq_sum
      have hlog_nonpos : Real.logb (nat_base b hb : ℝ) (q e) ≤ 0 := by
        exact (Real.logb_le_iff_le_rpow (nat_base_one_lt b hb) (hq_pos e)).2 (by simpa)
      linarith
    exact (Nat.ceil_lt_add_one hnonneg).le
  have hkraft : ∑ e : E, ((1 / b : ℝ) ^ ℓ e) ≤ 1 := by
    -- Summing the pointwise `b`-adic bounds yields the Kraft inequality.
    refine le_trans ?_ hq_sum
    exact Finset.sum_le_sum fun e _ ↦ hpow_le e
  exact ⟨ℓ, hpow_le, hbound, hkraft⟩

/-- Helper for Exercise 5.3.5: any finite family can be assigned a uniform base-`b` tail depth
whose Kraft sum still fits inside a single `b`-ary subtree. -/
private theorem existsNatBaseTailLengths (b : ℕ) (hb : 2 ≤ b) {Z : Type*} [Fintype Z] :
    ∃ τ : Z → ℕ, ∑ z : Z, ((1 / b : ℝ) ^ τ z) ≤ 1 := by
  classical
  let n : ℕ := Fintype.card Z
  let τ : Z → ℕ := fun _ ↦ n
  have hcard_le_pow : n ≤ b ^ n := by
    exact le_trans n.lt_two_pow_self.le (Nat.pow_le_pow_left hb _)
  have hreal : (n : ℝ) * ((1 / b : ℝ) ^ n) ≤ 1 := by
    have hpow_pos : 0 < (b : ℝ) ^ n := by positivity
    have hcard_le_pow_real : (n : ℝ) ≤ (b : ℝ) ^ n := by
      exact_mod_cast hcard_le_pow
    have hdiv : (n : ℝ) / (b : ℝ) ^ n ≤ 1 := by
      refine (div_le_iff₀ hpow_pos).2 ?_
      simpa using hcard_le_pow_real
    simpa [one_div, inv_pow, div_eq_mul_inv, τ, n] using hdiv
  refine ⟨τ, ?_⟩
  -- All zero-mass symbols receive the same deep tail, so the Kraft sum is just a constant count.
  calc
    ∑ z : Z, ((1 / b : ℝ) ^ τ z) = (Fintype.card Z : ℝ) * ((1 / b : ℝ) ^ n) := by
      simp [τ, n]
    _ ≤ 1 := hreal

/-- Helper for Exercise 5.3.5: the Shannon ceiling length attached to a source symbol in base
`b`. -/
private noncomputable def shannonLengthInNatBase
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (e : E) : ℕ :=
  if p e = 0 then 0 else ⌈-Real.logb (nat_base b hb : ℝ) (p e).toReal⌉₊

/-- Helper for Exercise 5.3.5: on the support of `p`, the base-`b` Shannon ceiling length
satisfies the usual pointwise `+1` bound. -/
private theorem shannonLengthInNatBase_le_entropy_term [Finite E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (e : E) (hp : p e ≠ 0) :
    (shannonLengthInNatBase b hb p e : ℝ) ≤
      -Real.logb (nat_base b hb : ℝ) (p e).toReal + 1 := by
  -- The Shannon ceiling differs from the ideal base-`b` length by at most one digit.
  let _ : Fintype E := Fintype.ofFinite E
  have hq_pos : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
  have hq_le_one : (p e).toReal ≤ 1 := by
    calc
      (p e).toReal ≤ ∑ x : E, (p x).toReal := by
        simpa using Finset.single_le_sum (fun x _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ e)
      _ = 1 := sumToRealPmf p
  have hlog_nonpos : Real.logb (nat_base b hb : ℝ) (p e).toReal ≤ 0 := by
    exact (Real.logb_le_iff_le_rpow (nat_base_one_lt b hb) hq_pos).2 (by simpa)
  have hnonneg : 0 ≤ -Real.logb (nat_base b hb : ℝ) (p e).toReal := by
    linarith
  simpa [shannonLengthInNatBase, hp] using (Nat.ceil_lt_add_one hnonneg).le

/-- Helper for Exercise 5.3.5: on the support of `p`, the base-`b` Shannon ceiling length
produces a `b`-adic mass bounded above by `p`. -/
private theorem shannonMassInNatBase_le_toReal [Finite E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (e : E) (hp : p e ≠ 0) :
    ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p e) ≤ (p e).toReal := by
  -- Exponentiating the ceiling inequality gives the standard Shannon upper bound.
  let _ : Fintype E := Fintype.ofFinite E
  have hq_pos : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
  have hceil : -Real.logb (nat_base b hb : ℝ) (p e).toReal ≤ shannonLengthInNatBase b hb p e := by
    simpa [shannonLengthInNatBase, hp] using
      (Nat.le_ceil (-Real.logb (nat_base b hb : ℝ) (p e).toReal))
  have hpow :
      ((nat_base b hb : ℝ) ^ (-(shannonLengthInNatBase b hb p e : ℝ))) ≤ (p e).toReal := by
    have hle_log : (-(shannonLengthInNatBase b hb p e : ℝ)) ≤
        Real.logb (nat_base b hb : ℝ) (p e).toReal := by
      linarith
    exact (Real.le_logb_iff_rpow_le (nat_base_one_lt b hb) hq_pos).mp hle_log
  calc
    ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p e) =
        ((1 / b : ℝ) ^ (shannonLengthInNatBase b hb p e : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = (((nat_base b hb : ℝ)⁻¹) ^ (shannonLengthInNatBase b hb p e : ℝ)) := by
      change ((1 / (b : ℝ)) ^ (shannonLengthInNatBase b hb p e : ℝ)) =
        (((b : ℝ)⁻¹) ^ (shannonLengthInNatBase b hb p e : ℝ))
      rw [one_div]
    _ = ((nat_base b hb : ℝ) ^ (-(shannonLengthInNatBase b hb p e : ℝ))) := by
      exact
        (Real.rpow_neg_eq_inv_rpow (nat_base b hb : ℝ)
          (shannonLengthInNatBase b hb p e : ℝ)).symm
    _ ≤ (p e).toReal := hpow

/-- Helper for Exercise 5.3.5: the real masses of `p` still sum to `1` after restricting to the
positive support. -/
private theorem sumToRealPmfOnSupport [Fintype E] (p : PMF E) :
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
      _ = 1 := sumToRealPmf p
  have hzero :
      ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hp : p e = 0 := by simpa using he
    simp [hp]
  linarith

/-- Helper for Exercise 5.3.5: if the support Shannon `b`-adic masses already saturate the full
tree, then they agree termwise with the source masses. -/
private theorem supportShannonLengthsInNatBase_eq_p_of_kraft_eq_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E)
    (hKraft :
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0),
        ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p e)) = 1) :
    ∀ e, p e ≠ 0 → ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p e) = (p e).toReal := by
  -- Equality of the total sums forces equality of each nonnegative support deficit.
  intro e hp
  let NZ : Finset E := Finset.univ.filter fun x ↦ p x ≠ 0
  let d : E → ℝ := fun x ↦ (p x).toReal - ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p x)
  have hd_nonneg : ∀ x ∈ NZ, 0 ≤ d x := by
    intro x hx
    have hx' : p x ≠ 0 := by simpa [NZ] using hx
    exact sub_nonneg.mpr (shannonMassInNatBase_le_toReal b hb p x hx')
  have hsum_d : ∑ x ∈ NZ, d x = 0 := by
    calc
      ∑ x ∈ NZ, d x =
          (∑ x ∈ NZ, (p x).toReal) -
            ∑ x ∈ NZ, ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p x) := by
        simp [NZ, d, Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [sumToRealPmfOnSupport p, hKraft]
      _ = 0 := by ring
  have heq_zero :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x hx ↦ hd_nonneg x hx)).1 hsum_d e (by
      simpa [NZ] using hp)
  dsimp [d] at heq_zero
  linarith

/-- Helper for Exercise 5.3.5: removing the zero-mass symbols does not change the finite
base-`b` entropy sum. -/
private theorem entropyInNatBase_toReal_eq_support_sum [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    (entropyInBase (nat_base b hb) p).toReal =
      -∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0),
        (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal := by
  let Z : Finset E := Finset.univ.filter fun e ↦ p e = 0
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  let f : E → ℝ := fun e ↦ (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal
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
  rw [entropyInBase_toReal_eq_sum, hsupport]

/-- Helper for Exercise 5.3.5: the Shannon support lengths already satisfy the standard
`H_b + 1` expected-length bound. -/
private theorem shannonSupportExpectedLengthInNatBase_le_entropy_add_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0),
      (p e).toReal * (shannonLengthInNatBase b hb p e : ℝ)) ≤
        (entropyInBase (nat_base b hb) p).toReal + 1 := by
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  -- Apply the pointwise Shannon ceiling estimate on the positive support and sum the result.
  calc
    ∑ e ∈ NZ, (p e).toReal * (shannonLengthInNatBase b hb p e : ℝ) ≤
        ∑ e ∈ NZ,
          (-((p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal) + (p e).toReal) := by
      refine Finset.sum_le_sum ?_
      intro e he
      have hp : p e ≠ 0 := by simpa [NZ] using he
      have hmul :
          (p e).toReal * (shannonLengthInNatBase b hb p e : ℝ) ≤
            (p e).toReal * (-Real.logb (nat_base b hb : ℝ) (p e).toReal + 1) := by
        exact mul_le_mul_of_nonneg_left
          (shannonLengthInNatBase_le_entropy_term b hb p e hp) ENNReal.toReal_nonneg
      nlinarith
    _ = (-∑ e ∈ NZ, (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal) +
          ∑ e ∈ NZ, (p e).toReal := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_neg_distrib]
    _ = (entropyInBase (nat_base b hb) p).toReal + 1 := by
      rw [entropyInNatBase_toReal_eq_support_sum b hb p, sumToRealPmfOnSupport p]

/-- Helper for Exercise 5.3.5: when the support Shannon Kraft sum saturates the full `b`-ary
tree, the support Shannon expected length is exactly `H_b(p)`. -/
private theorem shannonSupportExpectedLengthInNatBase_eq_entropy_of_kraft_eq_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E)
    (hKraft :
      (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0),
        ((1 / b : ℝ) ^ shannonLengthInNatBase b hb p e)) = 1) :
    (∑ e ∈ Finset.univ.filter (fun e ↦ p e ≠ 0),
      (p e).toReal * (shannonLengthInNatBase b hb p e : ℝ)) =
        (entropyInBase (nat_base b hb) p).toReal := by
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  have hmass := supportShannonLengthsInNatBase_eq_p_of_kraft_eq_one b hb p hKraft
  -- Rewrite each support term using the exact `b`-adic identity
  -- supplied by the saturated Kraft sum.
  calc
    ∑ e ∈ NZ, (p e).toReal * (shannonLengthInNatBase b hb p e : ℝ) =
        ∑ e ∈ NZ, -((p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      have hp : p e ≠ 0 := by simpa [NZ] using he
      have hlog :
          Real.logb (nat_base b hb : ℝ) (p e).toReal =
            -(shannonLengthInNatBase b hb p e : ℝ) := by
        have hself : Real.logb (nat_base b hb : ℝ) (b : ℝ) = 1 := by
          simpa using Real.logb_self_eq_one (nat_base_one_lt b hb)
        rw [← hmass e hp, Real.logb_pow, one_div, Real.logb_inv, hself]
        ring
      rw [hlog]
      ring
    _ = (entropyInBase (nat_base b hb) p).toReal := by
      calc
        ∑ e ∈ NZ, -((p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal) =
            -∑ e ∈ NZ, (p e).toReal * Real.logb (nat_base b hb : ℝ) (p e).toReal := by
          rw [← Finset.sum_neg_distrib]
        _ = (entropyInBase (nat_base b hb) p).toReal := by
          exact (entropyInNatBase_toReal_eq_support_sum b hb p).symm

/-- Helper for Exercise 5.3.5: there is a full base-`b` length family whose Kraft sum is at most
`1` and whose `p`-expected length is at most `H_b(p) + 1`. -/
private theorem existsNatBaseLengthsExpectedLengthLeEntropyAddOne [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    ∃ ℓ : E → ℕ,
      (∑ e : E, ((1 / b : ℝ) ^ ℓ e) ≤ 1) ∧
      (∑ e : E, (p e).toReal * (ℓ e : ℝ) ≤ (entropyInBase (nat_base b hb) p).toReal + 1) := by
  classical
  let NZ : Finset E := Finset.univ.filter fun e ↦ p e ≠ 0
  let Z0 := {e : E // p e = 0}
  let m : E → ℕ := shannonLengthInNatBase b hb p
  let K : ℝ := ∑ e ∈ NZ, ((1 / b : ℝ) ^ m e)
  have hK_le : K ≤ 1 := by
    -- The Shannon support masses are pointwise bounded by `p`, so their sum is at most `1`.
    calc
      K = ∑ e ∈ NZ, ((1 / b : ℝ) ^ m e) := rfl
      _ ≤ ∑ e ∈ NZ, (p e).toReal := by
        refine Finset.sum_le_sum ?_
        intro e he
        have hp : p e ≠ 0 := by simpa [NZ] using he
        simpa [m] using shannonMassInNatBase_le_toReal b hb p e hp
      _ = 1 := sumToRealPmfOnSupport p
  have htail : ∃ τ : Z0 → ℕ, ∑ z : Z0, ((1 / b : ℝ) ^ τ z) ≤ 1 :=
    existsNatBaseTailLengths b hb
  rcases htail with ⟨τ, hτ⟩
  rcases lt_or_eq_of_le hK_le with hKlt | hKeq
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, ((1 / b : ℝ) ^ k) < 1 - K := by
      -- Strict slack in the support Kraft sum leaves room for a deep zero-mass tail.
      exact exists_pow_lt_of_lt_one (sub_pos.mpr hKlt) (by
        simpa [one_div] using inv_lt_one_of_one_lt₀ (nat_base_one_lt b hb))
    let ℓ : E → ℕ := fun e ↦
      if hp : p e = 0 then k + τ ⟨e, hp⟩ else m e
    refine ⟨ℓ, ?_, ?_⟩
    · have hzero_kraft :
          (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e)) ≤
            ((1 / b : ℝ) ^ k) := by
        -- Shift the generic zero-tail family to depth `k`; its Kraft mass scales by `b^{-k}`.
        calc
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e) =
              ∑ z ∈ Finset.subtype (fun e ↦ p e = 0) Finset.univ,
                ((1 / b : ℝ) ^ (k + τ z)) := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            apply Finset.sum_congr rfl
            intro z hz
            simp [ℓ, z.2]
          _ = ∑ z : Z0, ((1 / b : ℝ) ^ (k + τ z)) := by
            simp [Z0]
          _ = ((1 / b : ℝ) ^ k) * ∑ z : Z0, ((1 / b : ℝ) ^ τ z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            rw [pow_add]
          _ ≤ ((1 / b : ℝ) ^ k) * 1 := by
            gcongr
          _ = ((1 / b : ℝ) ^ k) := by ring
      have hsupport_kraft :
          ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) = K := by
        -- On the positive support, the length family is exactly the Shannon family.
        apply Finset.sum_congr rfl
        intro e he
        have hp : p e ≠ 0 := by simpa [NZ] using he
        simp [ℓ, hp, m]
      -- Split the Kraft sum into zero-mass and positive-support pieces.
      calc
        ∑ e : E, ((1 / b : ℝ) ^ ℓ e) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e)) +
              ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ ((1 / b : ℝ) ^ ℓ e)))
        _ ≤ ((1 / b : ℝ) ^ k) + K := by
          have hsupport_kraft_le : ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) ≤ K := by
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
        _ = ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by
          rw [hzero_exp, zero_add]
        _ = ∑ e ∈ NZ, (p e).toReal * (m e : ℝ) := hsupport_exp
        _ ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := by
          simpa [m] using shannonSupportExpectedLengthInNatBase_le_entropy_add_one b hb p
  · have hpos_atom : ∃ e₀ : E, p e₀ ≠ 0 := by
      -- A probability measure with total mass `1` must have a positive-support atom.
      by_contra hnone
      push Not at hnone
      have hsum_zero : (∑ e : E, (p e).toReal) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        simp [hnone e]
      rw [sumToRealPmf p] at hsum_zero
      norm_num at hsum_zero
    rcases hpos_atom with ⟨e₀, he₀⟩
    let ℓ : E → ℕ := fun e ↦
      if hp : p e = 0 then m e₀ + 1 + τ ⟨e, hp⟩ else if e = e₀ then m e + 1 else m e
    refine ⟨ℓ, ?_, ?_⟩
    · have hzero_kraft :
          (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e)) ≤
            ((1 / b : ℝ) ^ (m e₀ + 1)) := by
        -- The zero-mass tail sits inside the sibling subtree freed at depth `m e₀ + 1`.
        calc
          ∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e) =
              ∑ z ∈ Finset.subtype (fun e ↦ p e = 0) Finset.univ,
                ((1 / b : ℝ) ^ (m e₀ + 1 + τ z)) := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            apply Finset.sum_congr rfl
            intro z hz
            simp [ℓ, z.2]
          _ = ∑ z : Z0, ((1 / b : ℝ) ^ (m e₀ + 1 + τ z)) := by
            simp [Z0]
          _ = ((1 / b : ℝ) ^ (m e₀ + 1)) * ∑ z : Z0, ((1 / b : ℝ) ^ τ z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            rw [pow_add]
          _ ≤ ((1 / b : ℝ) ^ (m e₀ + 1)) * 1 := by
            gcongr
          _ = ((1 / b : ℝ) ^ (m e₀ + 1)) := by ring
      have he₀_mem_NZ : e₀ ∈ NZ := by simp [NZ, he₀]
      have hsupport_kraft :
          ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) =
            K - ((1 / b : ℝ) ^ m e₀) + ((1 / b : ℝ) ^ (m e₀ + 1)) := by
        -- Lengthening one support atom by one digit removes all but one child subtree.
        calc
          ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) =
              ((1 / b : ℝ) ^ ℓ e₀) + ∑ e ∈ NZ.erase e₀, ((1 / b : ℝ) ^ ℓ e) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_erase_add NZ (fun e ↦ ((1 / b : ℝ) ^ ℓ e)) he₀_mem_NZ).symm
          _ = ((1 / b : ℝ) ^ (m e₀ + 1)) + ∑ e ∈ NZ.erase e₀, ((1 / b : ℝ) ^ m e) := by
            congr 1
            · simp [ℓ, he₀]
            · apply Finset.sum_congr rfl
              intro e he
              have hp : p e ≠ 0 := by
                simpa [NZ] using (Finset.mem_of_mem_erase he)
              have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
              simp [ℓ, hp, hne, m]
          _ = K - ((1 / b : ℝ) ^ m e₀) + ((1 / b : ℝ) ^ (m e₀ + 1)) := by
            have hKsplit :
                K = ((1 / b : ℝ) ^ m e₀) + ∑ e ∈ NZ.erase e₀, ((1 / b : ℝ) ^ m e) := by
              rw [show K = ∑ e ∈ NZ, ((1 / b : ℝ) ^ m e) by rfl]
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add NZ (fun e ↦ ((1 / b : ℝ) ^ m e)) he₀_mem_NZ).symm
            linarith
      -- The freed sibling subtree has exactly the same Kraft mass as the lengthened child cylinder.
      calc
        ∑ e : E, ((1 / b : ℝ) ^ ℓ e) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), ((1 / b : ℝ) ^ ℓ e)) +
              ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ ((1 / b : ℝ) ^ ℓ e)))
        _ ≤ ((1 / b : ℝ) ^ (m e₀ + 1)) +
              (K - ((1 / b : ℝ) ^ m e₀) + ((1 / b : ℝ) ^ (m e₀ + 1))) := by
          have hsupport_kraft_le :
              ∑ e ∈ NZ, ((1 / b : ℝ) ^ ℓ e) ≤
                K - ((1 / b : ℝ) ^ m e₀) + ((1 / b : ℝ) ^ (m e₀ + 1)) := by
            rw [hsupport_kraft]
          linarith
        _ ≤ K := by
          have hpow_nonneg : 0 ≤ ((1 / b : ℝ) ^ m e₀) := by positivity
          have hb_two : (2 : ℝ) ≤ b := by
            exact_mod_cast hb
          have hb_inv : (1 / b : ℝ) ≤ (1 / 2 : ℝ) := by
            have hb_ne : (b : ℝ) ≠ 0 := by positivity
            norm_num
            field_simp [hb_ne]
            nlinarith
          have hpair :
              ((1 / b : ℝ) ^ m e₀) * (1 / b : ℝ) +
                  ((1 / b : ℝ) ^ m e₀) * (1 / b : ℝ) ≤
                ((1 / b : ℝ) ^ m e₀) := by
            nlinarith
          have hsucc : ((1 / b : ℝ) ^ (m e₀ + 1)) = ((1 / b : ℝ) ^ m e₀) * (1 / b : ℝ) := by
            rw [pow_succ]
          linarith
        _ ≤ 1 := by simp [hKeq]
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
        -- The only change on the support is the one extra digit assigned to `e₀`.
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
          _ = 1 := sumToRealPmf p
      -- The saturated Shannon support already has entropy cost exactly `H_b`;
      -- only one extra digit remains.
      calc
        ∑ e : E, (p e).toReal * (ℓ e : ℝ) =
            (∑ e ∈ Finset.univ.filter (fun e ↦ p e = 0), (p e).toReal * (ℓ e : ℝ)) +
              ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by
          symm
          simpa [NZ] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ (fun e ↦ p e = 0)
              (fun e ↦ (p e).toReal * (ℓ e : ℝ)))
        _ = ∑ e ∈ NZ, (p e).toReal * (ℓ e : ℝ) := by
          rw [hzero_exp, zero_add]
        _ = (∑ e ∈ NZ, (p e).toReal * (m e : ℝ)) + (p e₀).toReal := hsupport_exp
        _ = (entropyInBase (nat_base b hb) p).toReal + (p e₀).toReal := by
          simpa [m] using
            shannonSupportExpectedLengthInNatBase_eq_entropy_of_kraft_eq_one b hb p hKeq
        _ ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := by
          gcongr

/-- Helper for Exercise 5.3.5: `digitString b l n` is the fixed-length big-endian base-`b`
expansion of `n`, padded with leading zeros up to length `l`. -/
private def digitString (b l n : ℕ) : List ℕ :=
  (Nat.digitsAppend b l n).reverse

/-- Helper for Exercise 5.3.5: a fixed-length base-`b` digit string has the prescribed length
whenever the represented number fits into `l` digits. -/
private theorem digitString_length (b : ℕ) (hb : 2 ≤ b) {l n : ℕ} (hn : n < b ^ l) :
    (digitString b l n).length = l := by
  -- Reverse does not change the padded digit-string length.
  have hb' : 1 < b := lt_of_lt_of_le one_lt_two hb
  simpa [digitString] using Nat.length_digitsAppend hb' l hn

/-- Helper for Exercise 5.3.5: every digit occurring in `digitString b l n` lies in
`{0, ..., b - 1}`. -/
private theorem digitString_digit_lt (b : ℕ) (hb : 2 ≤ b) {l n d : ℕ}
    (hd : d ∈ digitString b l n) : d < b := by
  -- Reverse preserves membership, so the bound comes from `Nat.digitsAppend`.
  have hb' : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hd' : d ∈ Nat.digitsAppend b l n := by
    simpa [digitString] using List.mem_reverse.mp hd
  exact Nat.lt_of_mem_digitsAppend hb' l d hd'

/-- Helper for Exercise 5.3.5: splitting a padded little-endian base-`b` digit expansion at a
suffix length corresponds to quotient and remainder by `b ^ m`. -/
private theorem digitsAppend_split (b : ℕ) (hb : 2 ≤ b) (n m x : ℕ)
    (hx : x < b ^ (n + m)) :
    Nat.digitsAppend b (n + m) x =
      Nat.digitsAppend b m (x % b ^ m) ++ Nat.digitsAppend b n (x / b ^ m) := by
  -- Compare both sides after decoding them with `Nat.ofDigits` on the fixed-length digit space.
  have hb' : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_two hb
  have hmod : x % b ^ m < b ^ m := Nat.mod_lt _ (pow_pos hb_pos _)
  have hdiv : x / b ^ m < b ^ n := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hb_pos m)]
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hx
  apply (Nat.injOn_ofDigits hb' (n + m))
  · refine ⟨Nat.length_digitsAppend hb' (n + m) hx, ?_⟩
    intro d hd
    exact Nat.lt_of_mem_digitsAppend hb' (n + m) d hd
  · refine ⟨?_, ?_⟩
    · rw [List.length_append]
      rw [Nat.length_digitsAppend hb' m hmod, Nat.length_digitsAppend hb' n hdiv]
      omega
    · intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · exact Nat.lt_of_mem_digitsAppend hb' m d hd
      · exact Nat.lt_of_mem_digitsAppend hb' n d hd
  · -- Decode both sides and use `x = x % b^m + b^m * (x / b^m)`.
    calc
      Nat.ofDigits b (Nat.digitsAppend b (n + m) x) = x := by
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
      _ = x % b ^ m + b ^ m * (x / b ^ m) := by
        symm
        exact Nat.mod_add_div x (b ^ m)
      _ = Nat.ofDigits b
            (Nat.digitsAppend b m (x % b ^ m) ++ Nat.digitsAppend b n (x / b ^ m)) := by
        rw [Nat.ofDigits_append, Nat.length_digitsAppend hb' m hmod]
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- Helper for Exercise 5.3.5: splitting a big-endian fixed-length base-`b` digit string into a
prefix and suffix corresponds to quotient and remainder by the appropriate power of `b`. -/
private theorem digitString_split (b : ℕ) (hb : 2 ≤ b) (n m x : ℕ)
    (hx : x < b ^ (n + m)) :
    digitString b (n + m) x =
      digitString b n (x / b ^ m) ++ digitString b m (x % b ^ m) := by
  -- Reverse the little-endian split so the quotient becomes the big-endian prefix.
  simpa [digitString, List.reverse_append] using congrArg List.reverse
    (digitsAppend_split b hb n m x hx)

/-- Helper for Exercise 5.3.5: fixed-length base-`b` digit strings are injective on numbers that
fit into the chosen length. -/
private theorem digitString_injective (b : ℕ) (_hb : 2 ≤ b) {l x y : ℕ}
    (_hx : x < b ^ l) (_hy : y < b ^ l) (hxy : digitString b l x = digitString b l y) : x = y := by
  -- Decode the reversed padded digit strings with `Nat.ofDigits`.
  have hdigits : Nat.digitsAppend b l x = Nat.digitsAppend b l y := by
    simpa [digitString] using congrArg List.reverse hxy
  have hdecode := congrArg (Nat.ofDigits b) hdigits
  simpa [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits] using hdecode

/-- Helper for Exercise 5.3.5: coerce a natural digit to `Fin b`, sending out-of-range values to
`0`. On the codewords built below, only the in-range branch is used. -/
private def digitToFin (b : ℕ) (hb : 0 < b) (d : ℕ) : Fin b :=
  if hd : d < b then ⟨d, hd⟩ else ⟨0, hb⟩

/-- Helper for Exercise 5.3.5: mapping admissible digits through `digitToFin` and then reading
their values recovers the original list. -/
private theorem map_val_map_digitToFin_eq (b : ℕ) (hb : 0 < b) {L : List ℕ}
    (hL : ∀ d ∈ L, d < b) :
    List.map Fin.val (List.map (digitToFin b hb) L) = L := by
  -- The fallback branch of `digitToFin` never occurs on a valid base-`b` digit list.
  induction L with
  | nil => rfl
  | cons d tl ih =>
      have hd : d < b := hL d (by simp)
      have htl : ∀ x ∈ tl, x < b := by
        intro x hx
        exact hL x (by simp [hx])
      simp [digitToFin, hd, ih htl]

/-- Helper for Exercise 5.3.5: a finite family of base-`b` lengths satisfying Kraft's inequality
can be realized by a `Fin b` prefix code with exactly those codeword lengths. -/
private theorem existsPrefixCodeOfNatBaseLengths [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (ℓ : E → ℕ) (hKraft : ∑ e : E, ((1 / b : ℝ) ^ ℓ e) ≤ 1) :
    ∃ C : PrefixCode (Fin b) E, ∀ e, (C.encode e).length = ℓ e := by
  classical
  -- Route correction: use the binary common-depth block construction with `2` replaced by `b`,
  -- and only transport to `Fin b` after the interval argument is complete.
  have hb' : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_two hb
  let N : ℕ := Finset.univ.sup ℓ
  let index : E → Fin (Fintype.card E) := Fintype.equivFin E
  let precedes : E → E → Prop := fun e₁ e₂ ↦
    ℓ e₁ < ℓ e₂ ∨ (ℓ e₁ = ℓ e₂ ∧ index e₁ < index e₂)
  let predecessors : E → Finset E := fun e ↦ Finset.univ.filter fun e' ↦ precedes e' e
  let blockWidth : E → ℕ := fun e ↦ b ^ (N - ℓ e)
  let blockIndex : E → ℕ := fun e ↦ Finset.sum (predecessors e) fun x ↦ b ^ (ℓ e - ℓ x)
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
    -- Each predecessor contributes one aligned base-`b` block at common depth `N`.
    dsimp [blockStart, blockIndex]
    simp only [blockWidth]
    rw [mul_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e' he'
    have hpred : precedes e' e := (Finset.mem_filter.mp he').2
    have hle : ℓ e' ≤ ℓ e := by
      rcases hpred with hlt | ⟨heq, _⟩
      · exact hlt.le
      · exact heq.le
    have hlen_le_N : ℓ e ≤ N := hlength_le e
    calc
      b ^ (N - ℓ e) * b ^ (ℓ e - ℓ e') = b ^ ((N - ℓ e) + (ℓ e - ℓ e')) := by
        rw [← Nat.pow_add]
      _ = b ^ (N - ℓ e') := by
        congr
        omega
      _ = blockWidth e' := by
        simp [blockWidth]
  have htotalWidth_nat : totalWidth ≤ b ^ N := by
    -- Multiply the Kraft inequality by `b ^ N` and rewrite the terms as block widths.
    have hb_ne : (b : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hb_pos)
    have hterm : ∀ e : E, ((1 / b : ℝ) ^ ℓ e) * (b : ℝ) ^ N = (blockWidth e : ℝ) := by
      intro e
      have hle : ℓ e ≤ N := hlength_le e
      calc
        ((1 / b : ℝ) ^ ℓ e) * (b : ℝ) ^ N = (1 / (b : ℝ) ^ ℓ e) * (b : ℝ) ^ N := by
          rw [one_div_pow]
        _ = (((b : ℝ) ^ ℓ e)⁻¹) * (b : ℝ) ^ N := by
          simp [one_div]
        _ = (b : ℝ) ^ (N - ℓ e) := by
          rw [mul_comm, ← pow_sub₀ (b : ℝ) hb_ne hle]
        _ = (blockWidth e : ℝ) := by
          simp [blockWidth]
    have hscaled := mul_le_mul_of_nonneg_right hKraft (by positivity : 0 ≤ (b : ℝ) ^ N)
    have hreal : (totalWidth : ℝ) ≤ (b : ℝ) ^ N := by
      calc
        (totalWidth : ℝ) = ∑ e : E, (blockWidth e : ℝ) := by
          simp [totalWidth]
        _ = ∑ e : E, (((1 / b : ℝ) ^ ℓ e) * (b : ℝ) ^ N) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hterm e]
        _ = (∑ e : E, ((1 / b : ℝ) ^ ℓ e)) * (b : ℝ) ^ N := by
          rw [Finset.sum_mul]
        _ ≤ 1 * (b : ℝ) ^ N := hscaled
        _ = (b : ℝ) ^ N := by ring
    exact_mod_cast hreal
  have hstart_step : ∀ {e₁ e₂ : E}, precedes e₁ e₂ →
      blockStart e₁ + blockWidth e₁ ≤ blockStart e₂ := by
    intro e₁ e₂ h₁₂
    -- Every earlier block of `e₁`, together with `e₁` itself, also sits before `e₂`.
    have hsubset : insert e₁ (predecessors e₁) ⊆ predecessors e₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁₂⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hprecedes_trans (Finset.mem_filter.mp hx).2 h₁₂⟩
    have hsum_le :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun x ↦ blockWidth x) hsubset fun x _ _ ↦ Nat.zero_le (blockWidth x)
    have hnot_mem : e₁ ∉ predecessors e₁ := by
      intro he
      exact hprecedes_irrefl e₁ (Finset.mem_filter.mp he).2
    calc
      blockStart e₁ + blockWidth e₁ =
          blockWidth e₁ + Finset.sum (predecessors e₁) fun x ↦ blockWidth x := by
        rw [hblockStart_sum, add_comm]
      _ = Finset.sum (insert e₁ (predecessors e₁)) fun x ↦ blockWidth x := by
        rw [Finset.sum_insert hnot_mem]
      _ ≤ Finset.sum (predecessors e₂) fun x ↦ blockWidth x := hsum_le
      _ = blockStart e₂ := (hblockStart_sum e₂).symm
  have hstartSucc_le_total : ∀ e : E, blockStart e + blockWidth e ≤ totalWidth := by
    intro e
    -- The current block and all earlier blocks belong to the full common-depth partition.
    have hsubset : insert e (predecessors e) ⊆ Finset.univ := by
      intro x hx
      simp
    have hsum_le :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun x ↦ blockWidth x) hsubset fun x _ _ ↦ Nat.zero_le (blockWidth x)
    have hnot_mem : e ∉ predecessors e := by
      intro he
      exact hprecedes_irrefl e (Finset.mem_filter.mp he).2
    calc
      blockStart e + blockWidth e =
          blockWidth e + Finset.sum (predecessors e) fun x ↦ blockWidth x := by
        rw [hblockStart_sum, add_comm]
      _ = Finset.sum (insert e (predecessors e)) fun x ↦ blockWidth x := by
        rw [Finset.sum_insert hnot_mem]
      _ ≤ Finset.sum Finset.univ fun x ↦ blockWidth x := hsum_le
      _ = totalWidth := by simp [totalWidth]
  have hblockIndex_lt : ∀ e : E, blockIndex e < b ^ ℓ e := by
    intro e
    -- The block for `e` must fit into the `b ^ N` leaves at depth `N`.
    have hfit : blockStart e + blockWidth e ≤ b ^ N :=
      le_trans (hstartSucc_le_total e) htotalWidth_nat
    have hrewrite : blockStart e + blockWidth e = (blockIndex e + 1) * blockWidth e := by
      simpa [blockStart] using (Nat.add_mul (blockIndex e) 1 (blockWidth e)).symm
    have hpow : b ^ N = (b ^ ℓ e) * blockWidth e := by
      have hlen_le_N : ℓ e ≤ N := hlength_le e
      simp only [blockWidth]
      rw [← Nat.pow_add]
      rw [Nat.add_comm, Nat.sub_add_cancel hlen_le_N]
    have hle : blockIndex e + 1 ≤ b ^ ℓ e := by
      apply Nat.le_of_mul_le_mul_right
      · simpa [hrewrite, hpow] using hfit
      · simp [blockWidth, hb_pos]
    exact Nat.lt_of_succ_le hle
  let encodeNat : E → List ℕ := fun e ↦ digitString b (ℓ e) (blockIndex e)
  let encode : E → List (Fin b) := fun e ↦ List.map (digitToFin b hb_pos) (encodeNat e)
  have hencodeNat_length : ∀ e : E, (encodeNat e).length = ℓ e := by
    intro e
    exact digitString_length b hb (hblockIndex_lt e)
  have hencodeNat_digit_lt : ∀ e : E, ∀ d ∈ encodeNat e, d < b := by
    intro e d hd
    exact digitString_digit_lt b hb hd
  have hencode_val : ∀ e : E, List.map Fin.val (encode e) = encodeNat e := by
    intro e
    exact map_val_map_digitToFin_eq b hb_pos (hencodeNat_digit_lt e)
  have hprefix_forces_interval : ∀ {e₁ e₂ : E}, encodeNat e₁ <+: encodeNat e₂ →
      blockStart e₂ < blockStart e₁ + blockWidth e₁ := by
    intro e₁ e₂ hprefix
    rcases hprefix with ⟨tail, htail⟩
    have hlen_le : ℓ e₁ ≤ ℓ e₂ := by
      have hlen := congrArg List.length htail
      rw [List.length_append, hencodeNat_length e₁, hencodeNat_length e₂] at hlen
      omega
    let d : ℕ := ℓ e₂ - ℓ e₁
    have hd : ℓ e₂ = ℓ e₁ + d := by
      simp [d, Nat.add_sub_of_le hlen_le]
    have hdiv_bound : blockIndex e₂ / b ^ d < b ^ ℓ e₁ := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hb_pos d)]
      calc
        blockIndex e₂ < b ^ ℓ e₂ := hblockIndex_lt e₂
        _ = b ^ (ℓ e₁ + d) := by simp [hd]
        _ = b ^ ℓ e₁ * b ^ d := by rw [Nat.pow_add]
    have htake :
        digitString b (ℓ e₁) (blockIndex e₁) = digitString b (ℓ e₁) (blockIndex e₂ / b ^ d) := by
      -- Compare the first `ℓ e₁` digits of the two decompositions of `encodeNat e₂`.
      have hsplit :
          encodeNat e₂ =
            digitString b (ℓ e₁) (blockIndex e₂ / b ^ d) ++
              digitString b d (blockIndex e₂ % b ^ d) := by
        simpa [encodeNat, hd] using
          (digitString_split b hb (ℓ e₁) d (blockIndex e₂)
            (by simpa [hd] using hblockIndex_lt e₂))
      have htake_left :
          List.take (ℓ e₁) (encodeNat e₂) = encodeNat e₁ := by
        rw [← htail, ← hencodeNat_length e₁]
        exact List.take_left
      have htake_right :
          List.take (ℓ e₁) (encodeNat e₂) =
            digitString b (ℓ e₁) (blockIndex e₂ / b ^ d) := by
        have hlen_div :
            (digitString b (ℓ e₁) (blockIndex e₂ / b ^ d)).length = ℓ e₁ :=
          digitString_length b hb hdiv_bound
        nth_rewrite 1 [← hlen_div]
        rw [hsplit]
        exact List.take_left
      simpa [encodeNat] using htake_left.symm.trans htake_right
    have hquot : blockIndex e₁ = blockIndex e₂ / b ^ d :=
      digitString_injective b hb (hblockIndex_lt e₁)
        hdiv_bound
        htake
    have hdiv_lt : blockIndex e₂ < (blockIndex e₁ + 1) * b ^ d := by
      rw [hquot]
      exact (Nat.div_lt_iff_lt_mul (pow_pos hb_pos d)).1 (Nat.lt_succ_self _)
    calc
      blockStart e₂ = blockIndex e₂ * b ^ (N - ℓ e₂) := by
        simp [blockStart, blockWidth]
      _ < ((blockIndex e₁ + 1) * b ^ d) * b ^ (N - ℓ e₂) := by
        exact (Nat.mul_lt_mul_right (pow_pos hb_pos _)).2 hdiv_lt
      _ = (blockIndex e₁ + 1) * b ^ (N - ℓ e₁) := by
        have hlen₂_le_N : ℓ e₂ ≤ N := hlength_le e₂
        have hexp : d + (N - ℓ e₂) = N - ℓ e₁ := by
          omega
        rw [Nat.mul_assoc, ← Nat.pow_add, hexp]
      _ = blockStart e₁ + blockWidth e₁ := by
        simpa [blockStart, blockWidth] using
          (Nat.add_mul (blockIndex e₁) 1 (b ^ (N - ℓ e₁)))
  refine ⟨{ encode := encode, prefix_free := ?_ }, ?_⟩
  · intro e₁ e₂ hne hprefix
    -- Reflect the `Fin b`-valued prefix back to natural digits
    -- and apply the interval argument there.
    have hprefix_nat : encodeNat e₁ <+: encodeNat e₂ := by
      rcases hprefix with ⟨tail, htail⟩
      refine ⟨List.map Fin.val tail, ?_⟩
      have htail' := congrArg (List.map Fin.val) htail
      rw [List.map_append, hencode_val e₁, hencode_val e₂] at htail'
      exact htail'
    have horder := hprecedes_total hne
    rcases horder with h₁₂ | h₂₁
    · exact (not_lt_of_ge (hstart_step h₁₂)) (hprefix_forces_interval hprefix_nat)
    · rcases h₂₁ with hlt | ⟨hlen, hidx⟩
      · rcases hprefix_nat with ⟨tail, htail⟩
        have hlen_le : ℓ e₁ ≤ ℓ e₂ := by
          have hlen' := congrArg List.length htail
          rw [List.length_append, hencodeNat_length e₁, hencodeNat_length e₂] at hlen'
          omega
        exact (not_lt_of_ge hlen_le) hlt
      · have hsameLength : ℓ e₁ = ℓ e₂ := hlen.symm
        have hprefix_eq : encodeNat e₁ = encodeNat e₂ := by
          rcases hprefix_nat with ⟨tail, htail⟩
          have htail_nil : tail = [] := by
            have htail_length : tail.length = 0 := by
              have hlengths := congrArg List.length htail
              rw [List.length_append, hencodeNat_length e₁,
                hencodeNat_length e₂, hsameLength] at hlengths
              omega
            exact List.eq_nil_iff_length_eq_zero.2 htail_length
          simpa [htail_nil] using htail
        have hindex_eq : blockIndex e₁ = blockIndex e₂ := by
          apply digitString_injective b hb
          · simpa [hsameLength] using hblockIndex_lt e₁
          · simpa [hsameLength] using hblockIndex_lt e₂
          · simpa [encodeNat, hsameLength] using hprefix_eq
        have hstart_eq : blockStart e₁ = blockStart e₂ := by
          simp [blockStart, blockWidth, hsameLength, hindex_eq]
        have hstrict : blockStart e₂ < blockStart e₁ := by
          have hpos : 0 < blockWidth e₂ := by
            simp [blockWidth, hb_pos]
          exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos)
            (hstart_step (Or.inr ⟨hlen, hidx⟩))
        exact (lt_irrefl _) (hstart_eq ▸ hstrict)
  · intro e
    simp [encode, hencodeNat_length e]

-- Proof sketch: choose Shannon lengths `l(e) = ⌈-log_b p(e)⌉`, verify the `b`-ary Kraft
-- inequality, and build a `b`-adic prefix code with these lengths to obtain the usual `+ 1`
-- overhead bound.
/-- Exercise 5.3.5 (2): for a finite alphabet, there exists a prefix code over `Fin b` whose
expected length is at most the base-`b` entropy `H_b(p)` plus `1`. -/
theorem exists_b_adic_prefix_code_expected_length_le_entropy_in_nat_base_add_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    ∃ C : PrefixCode (Fin b) E,
      C.expectedLength p ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := by
  -- Route correction: the entropy-side construction is now handled directly at the level of
  -- base-`b` lengths, so the theorem reduces to realizing those lengths as an actual prefix code.
  rcases existsNatBaseLengthsExpectedLengthLeEntropyAddOne b hb p with ⟨ℓ, hKraft, hExp⟩
  rcases existsPrefixCodeOfNatBaseLengths b hb ℓ hKraft with ⟨C, hlen⟩
  refine ⟨C, ?_⟩
  -- Rewrite the expected code length using the exact codeword-length realization.
  calc
    C.expectedLength p = ∑ e : E, (p e).toReal * (ℓ e : ℝ) := by
      rw [PrefixCode.expectedLength_def]
      apply Finset.sum_congr rfl
      intro e he
      rw [hlen e]
    _ ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := hExp
