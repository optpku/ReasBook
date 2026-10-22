/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part19

section Chap06
section Section30

/-- Helper for Theorem 6.30.22: reindexing a family on `Fin (m + 1)` as its last block together
with its tail rewrites the corresponding infimum as an infimum over a product. -/
lemma helperForTheorem_6_30_22_iInf_snoc_eq_iInf_prod
    {m : ℕ} {α : Type*} (H : (Fin (m + 1) → α) → EReal) :
    (⨅ z : Fin (m + 1) → α, H z) =
      (⨅ p : α × (Fin m → α), H (Fin.snoc p.2 p.1)) := by
  -- Reindex the family choices by the canonical `Fin.snocEquiv`.
  simpa using
    (Equiv.iInf_congr (Fin.snocEquiv (fun _ : Fin (m + 1) => α)).symm
      (f := H)
      (g := fun p : α × (Fin m → α) => H (Fin.snoc p.2 p.1))
      (fun z => by
        simp [Fin.snocEquiv_symm_apply]))

/-- Helper for Theorem 6.30.22: if each factor admits one finite witness, then the infimum of a
two-variable separable sum splits as the sum of the one-variable infima. -/
lemma helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
    {α β : Type*} [Nonempty α] [Nonempty β] (F : α → EReal) (G : β → EReal)
    (hF : ∃ a0, F a0 < ⊤) (hG : ∃ b0, G b0 < ⊤) :
    (⨅ p : α × β, F p.1 + G p.2) = (⨅ a, F a) + (⨅ b, G b) := by
  refine le_antisymm ?_ ?_
  · -- Approximate each one-variable infimum from above, then evaluate the product infimum at
    -- the corresponding pair.
    refine EReal.le_add_of_forall_gt ?_ ?_ ?_
    · rcases hG with ⟨b0, hb0⟩
      exact Or.inr (ne_of_lt <| lt_of_le_of_lt (iInf_le G b0) hb0)
    · rcases hF with ⟨a0, ha0⟩
      exact Or.inl (ne_of_lt <| lt_of_le_of_lt (iInf_le F a0) ha0)
    · intro a' ha' b' hb'
      rcases (iInf_lt_iff.mp ha') with ⟨a, ha⟩
      rcases (iInf_lt_iff.mp hb') with ⟨b, hb⟩
      exact le_trans
        (iInf_le (fun p : α × β => F p.1 + G p.2) (a, b))
        (add_le_add ha.le hb.le)
  · -- Every product value dominates the sum of the two coordinatewise infima.
    refine le_iInf ?_
    intro p
    exact add_le_add (iInf_le F p.1) (iInf_le G p.2)

/-- Helper for Theorem 6.30.22: the infimum of a finite sum of independent translated blocks
splits into the sum of the blockwise infima once each block has a finite witness. -/
lemma helperForTheorem_6_30_22_family_iInf_sum_eq_sum_iInf
    {m n : ℕ}
    (g : Fin m → (Fin n → ℝ) → EReal)
    (hfinite : ∀ i : Fin m, ∃ x : Fin n → ℝ, g i x < (⊤ : EReal)) :
    (⨅ z : Fin m → Fin n → ℝ, ∑ i : Fin m, g i (z i)) =
      ∑ i : Fin m, (⨅ x : Fin n → ℝ, g i x) := by
  induction m with
  | zero =>
      -- With no blocks there is only the empty family, so both sides are the empty sum.
      simp
  | succ m ih =>
      -- Reindex the family choice by its last block together with the tail family.
      rw [helperForTheorem_6_30_22_iInf_snoc_eq_iInf_prod
        (H := fun z : Fin (m + 1) → Fin n → ℝ => ∑ i : Fin (m + 1), g i (z i))]
      have hRewrite :
          (⨅ p : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
              ∑ i : Fin (m + 1),
                g i (@Fin.snoc m (fun _ : Fin (m + 1) => Fin n → ℝ) p.2 p.1 i)) =
            (⨅ p : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) := by
        -- Splitting the `Fin (m + 1)` sum isolates the last coordinate from the tail family.
        refine iInf_congr ?_
        intro p
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hRewrite]
      have hTailWitness :
          ∃ y : Fin m → Fin n → ℝ,
            (∑ i : Fin m, g (Fin.castSucc i) (y i)) < (⊤ : EReal) := by
        -- Choose a finite witness independently for each tail block and sum them.
        refine ⟨fun i => Classical.choose (hfinite (Fin.castSucc i)), ?_⟩
        exact lt_of_le_of_ne le_top <|
          finset_sum_ne_top_of_forall (s := Finset.univ)
            (f := fun i : Fin m => g (Fin.castSucc i) (Classical.choose (hfinite (Fin.castSucc i))))
            (fun i _ => ne_of_lt (Classical.choose_spec (hfinite (Fin.castSucc i))))
      have hLastWitness :
          ∃ x : Fin n → ℝ, g (Fin.last m) x < (⊤ : EReal) :=
        hfinite (Fin.last m)
      have hCommute :
          (⨅ p : (Fin n → ℝ) × (Fin m → Fin n → ℝ),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) =
            (⨅ p : (Fin m → Fin n → ℝ) × (Fin n → ℝ),
              (∑ i : Fin m, g (Fin.castSucc i) (p.1 i)) + g (Fin.last m) p.2) := by
        -- Swap the product coordinates so the two-factor splitting lemma applies directly.
        refine (Equiv.iInf_congr (Equiv.prodComm (Fin n → ℝ) (Fin m → Fin n → ℝ)) ?_)
        intro p
        simp [add_comm]
      rw [hCommute]
      rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun z : Fin m → Fin n → ℝ => ∑ i : Fin m, g (Fin.castSucc i) (z i))
        (G := fun y : Fin n → ℝ => g (Fin.last m) y)
        hTailWitness hLastWitness]
      let gTail : Fin m → (Fin n → ℝ) → EReal := fun i => g (Fin.castSucc i)
      have hTailFinite : ∀ i : Fin m, ∃ x : Fin n → ℝ, gTail i x < (⊤ : EReal) := by
        -- The tail family inherits the finite witnesses from the original family.
        intro i
        exact hfinite (Fin.castSucc i)
      rw [show
          (⨅ z : Fin m → Fin n → ℝ, ∑ i : Fin m, g (Fin.castSucc i) (z i)) =
            ∑ i : Fin m, (⨅ x : Fin n → ℝ, g (Fin.castSucc i) x) by
              simpa [gTail] using ih gTail hTailFinite]
      -- Reassemble the head-tail decomposition into the full finite sum.
      simp [Fin.sum_univ_castSucc, add_comm]

/-- Helper for Theorem 6.30.22: if the coefficient of a real linear form is nonzero, then the
infimum of any finite affine translate of that form is `-∞`. -/
lemma helperForTheorem_6_30_22_sInf_linear_term_eq_bot_of_ne_zero_with_realConst
    {n : ℕ} (b : Fin n → ℝ) (r : ℝ) (hb : b ≠ 0) :
    sInf (Set.range fun x : Fin n → ℝ => ((((x ⬝ᵥ b : ℝ) + r : ℝ) : EReal))) = (⊥ : EReal) := by
  -- Drive the linear form to `-∞` along the ray `x = -t • b`.
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  have hq_nonneg : 0 ≤ (b ⬝ᵥ b : ℝ) := by
    simp [dotProduct]
    exact Finset.sum_nonneg (fun i _ => by nlinarith [sq_nonneg (b i)])
  have hq_ne : (b ⬝ᵥ b : ℝ) ≠ 0 := by
    intro hzero
    exact hb ((dotProduct_self_eq_zero).mp hzero)
  have hq_pos : 0 < (b ⬝ᵥ b : ℝ) := lt_of_le_of_ne hq_nonneg hq_ne.symm
  let t : ℝ := |((r - y) / (b ⬝ᵥ b : ℝ))| + 1
  have hratio : ((r - y) / (b ⬝ᵥ b : ℝ)) < t := by
    -- The chosen scalar dominates the quotient by one unit.
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self ((r - y) / (b ⬝ᵥ b : ℝ))) ?_
    linarith [abs_nonneg ((r - y) / (b ⬝ᵥ b : ℝ))]
  have hmul : r - y < t * (b ⬝ᵥ b : ℝ) := by
    exact (div_lt_iff₀ hq_pos).mp hratio
  have hreal : r - t * (b ⬝ᵥ b : ℝ) < y := by
    linarith
  have hwitness :
      sInf (Set.range fun x : Fin n → ℝ => ((((x ⬝ᵥ b : ℝ) + r : ℝ) : EReal))) ≤
        (((r - t * (b ⬝ᵥ b : ℝ) : ℝ) : EReal)) := by
    -- Evaluate the infimum at the explicit ray point `x = -t • b`.
    refine sInf_le ?_
    refine ⟨fun i => -(t * b i), ?_⟩
    have hdot : (((fun i => -(t * b i)) ⬝ᵥ b : ℝ) + r) = r - t * (b ⬝ᵥ b : ℝ) := by
      calc
        (((fun i => -(t * b i)) ⬝ᵥ b : ℝ) + r)
            = (-t * (b ⬝ᵥ b : ℝ)) + r := by
                simp [dotProduct, Finset.mul_sum]
                ring_nf
        _ = r - t * (b ⬝ᵥ b : ℝ) := by ring
    simp [hdot]
  refine lt_of_le_of_lt hwitness ?_
  exact_mod_cast hreal

/-- Helper for Theorem 6.30.22: adding a finite real constant commutes with an indexed infimum
in `EReal`. -/
lemma helperForTheorem_6_30_22_iInf_add_realConst
    {α : Type*} (G : α → EReal) (c : ℝ) :
    (⨅ a, G a + ((c : ℝ) : EReal)) = (⨅ a, G a) + ((c : ℝ) : EReal) := by
  -- Addition by a real constant is an order isomorphism on `EReal`.
  exact (OrderIso.map_iInf (section13_addRightOrderIso c) G).symm

/-- Helper for Theorem 6.30.22: a product infimum of the form `F + G + c` splits into the
factorwise infima, after which the real constant `c` may be pulled outside. -/
lemma helperForTheorem_6_30_22_twoFactor_iInf_add_realConst
    {α β : Type*} [Nonempty α] [Nonempty β] (F : α → EReal) (G : β → EReal)
    (c : ℝ) (hF : ∃ a0, F a0 < ⊤) (hG : ∃ b0, G b0 < ⊤) :
    (⨅ q : α × β, F q.1 + G q.2 + ((c : ℝ) : EReal)) =
      ((⨅ a, F a) + (⨅ b, G b)) + ((c : ℝ) : EReal) := by
  -- Reassociate the constant into the second factor so the existing product-splitting lemma
  -- applies directly.
  have hAssoc :
      (⨅ q : α × β, F q.1 + G q.2 + ((c : ℝ) : EReal)) =
        (⨅ q : α × β, F q.1 + (G q.2 + ((c : ℝ) : EReal))) := by
    refine iInf_congr ?_
    intro q
    simp [add_assoc]
  rw [hAssoc]
  have hG' : ∃ b0, G b0 + ((c : ℝ) : EReal) < ⊤ := by
    rcases hG with ⟨b0, hb0⟩
    exact ⟨b0, EReal.add_lt_top (ne_of_lt hb0) (EReal.coe_ne_top _)⟩
  rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
    (F := F) (G := fun b => G b + ((c : ℝ) : EReal)) hF hG']
  rw [helperForTheorem_6_30_22_iInf_add_realConst (G := G) (c := c)]
  simp [add_assoc]

/-- Helper for Theorem 6.30.22: an infimum over a product can be rewritten as nested infima over
the two coordinates. -/
lemma helperForTheorem_6_30_22_iInf_prod_eq_nested
    {α β : Type*} (H : α → β → EReal) :
    (⨅ p : α × β, H p.1 p.2) = (⨅ a : α, ⨅ b : β, H a b) := by
  -- The product infimum and the iterated infimum bound each other by evaluating at pairs.
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro a
    refine le_iInf ?_
    intro b
    exact iInf_le (fun p : α × β => H p.1 p.2) (a, b)
  · refine le_iInf ?_
    intro p
    exact le_trans
      (iInf_le (fun a : α => ⨅ b : β, H a b) p.1)
      (iInf_le (fun b : β => H p.1 b) p.2)

/-- Helper for Theorem 6.30.22: a pair of `Fin m`-indexed families can be reindexed as a single
family of coordinate pairs inside the block-separable infimum. -/
lemma helperForTheorem_6_30_22_pairFamily_iInf_eq_familyPairs
    {m : ℕ} {α β : Type*} (H : Fin m → α → β → EReal) :
    (⨅ p : (Fin m → α) × (Fin m → β), ∑ i : Fin m, H i (p.1 i) (p.2 i)) =
      (⨅ z : Fin m → α × β, ∑ i : Fin m, H i (z i).1 (z i).2) := by
  -- Repackage the two global families as the single family of coordinate pairs.
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro z
    exact le_trans
      (iInf_le
        (fun p : (Fin m → α) × (Fin m → β) =>
          ∑ i : Fin m, H i (p.1 i) (p.2 i))
        (fun i => (z i).1, fun i => (z i).2))
      (by simp)
  · refine le_iInf ?_
    intro p
    exact le_trans
      (iInf_le
        (fun z : Fin m → α × β =>
          ∑ i : Fin m, H i (z i).1 (z i).2)
        (fun i => (p.1 i, p.2 i)))
      (by simp)

/-- Helper for Theorem 6.30.22: an infimum over enlarged perturbation parameters can be rewritten
as nested infima over the scalar perturbations, the base translation, and the family of shifted
translations. -/
lemma helperForTheorem_6_30_22_iInf_parameter_eq_nestedBlocks
    {m n : ℕ} (H : EnlargedPerturbationParameter m n → EReal) :
    (⨅ w : EnlargedPerturbationParameter m n, H w) =
      (⨅ u : Fin m → ℝ, ⨅ x0 : Fin n → ℝ, ⨅ xShift : Fin m → Fin n → ℝ,
        H { u := u, x0 := x0, xShift := xShift }) := by
  -- The structure infimum and the explicit block infimum dominate each other by evaluation.
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro u
    refine le_iInf ?_
    intro x0
    refine le_iInf ?_
    intro xShift
    exact iInf_le H { u := u, x0 := x0, xShift := xShift }
  · refine le_iInf ?_
    intro w
    exact le_trans
      (iInf_le (fun u : Fin m → ℝ =>
        ⨅ x0 : Fin n → ℝ, ⨅ xShift : Fin m → Fin n → ℝ,
          H { u := u, x0 := x0, xShift := xShift }) w.u)
      (le_trans
        (iInf_le (fun x0 : Fin n → ℝ =>
          ⨅ xShift : Fin m → Fin n → ℝ,
            H { u := w.u, x0 := x0, xShift := xShift }) w.x0)
        (iInf_le (fun xShift : Fin m → Fin n → ℝ =>
          H { u := w.u, x0 := w.x0, xShift := xShift }) w.xShift))

/-- Helper for Theorem 6.30.22: the infimum of a finite sum of independent blocks over any common
parameter space splits into the sum of the blockwise infima once each block has a finite witness. -/
lemma helperForTheorem_6_30_22_family_iInf_sum_eq_sum_iInf_generic
    {m : ℕ} {α : Type*} [Nonempty α]
    (g : Fin m → α → EReal)
    (hfinite : ∀ i : Fin m, ∃ a : α, g i a < (⊤ : EReal)) :
    (⨅ z : Fin m → α, ∑ i : Fin m, g i (z i)) =
      ∑ i : Fin m, (⨅ a : α, g i a) := by
  induction m with
  | zero =>
      -- With no blocks there is only the empty family, so both sides are the empty sum.
      simp
  | succ m ih =>
      -- Reindex the family by its last block together with the tail family.
      rw [helperForTheorem_6_30_22_iInf_snoc_eq_iInf_prod
        (H := fun z : Fin (m + 1) → α => ∑ i : Fin (m + 1), g i (z i))]
      have hRewrite :
          (⨅ p : α × (Fin m → α),
              ∑ i : Fin (m + 1), g i (@Fin.snoc m (fun _ : Fin (m + 1) => α) p.2 p.1 i)) =
            (⨅ p : α × (Fin m → α),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) := by
        -- Splitting the `Fin (m + 1)` sum isolates the final block.
        refine iInf_congr ?_
        intro p
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hRewrite]
      have hTailWitness :
          ∃ y : Fin m → α, (∑ i : Fin m, g (Fin.castSucc i) (y i)) < (⊤ : EReal) := by
        -- Choose a finite witness independently for each tail block and sum them.
        refine ⟨fun i => Classical.choose (hfinite (Fin.castSucc i)), ?_⟩
        exact lt_of_le_of_ne le_top <|
          finset_sum_ne_top_of_forall (s := Finset.univ)
            (f := fun i : Fin m => g (Fin.castSucc i) (Classical.choose (hfinite (Fin.castSucc i))))
            (fun i _ => ne_of_lt (Classical.choose_spec (hfinite (Fin.castSucc i))))
      have hLastWitness :
          ∃ a : α, g (Fin.last m) a < (⊤ : EReal) :=
        hfinite (Fin.last m)
      have hCommute :
          (⨅ p : α × (Fin m → α),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) =
            (⨅ p : (Fin m → α) × α,
              (∑ i : Fin m, g (Fin.castSucc i) (p.1 i)) + g (Fin.last m) p.2) := by
        -- Swap the product coordinates so the two-factor splitting lemma applies directly.
        refine (Equiv.iInf_congr (Equiv.prodComm α (Fin m → α)) ?_)
        intro p
        simp [add_comm]
      rw [hCommute]
      rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun z : Fin m → α => ∑ i : Fin m, g (Fin.castSucc i) (z i))
        (G := fun a : α => g (Fin.last m) a)
        hTailWitness hLastWitness]
      let gTail : Fin m → α → EReal := fun i => g (Fin.castSucc i)
      have hTailFinite : ∀ i : Fin m, ∃ a : α, gTail i a < (⊤ : EReal) := by
        -- The tail family inherits the same finite witnesses.
        intro i
        exact hfinite (Fin.castSucc i)
      rw [show
          (⨅ z : Fin m → α, ∑ i : Fin m, g (Fin.castSucc i) (z i)) =
            ∑ i : Fin m, (⨅ a : α, g (Fin.castSucc i) a) by
              simpa [gTail] using ih gTail hTailFinite]
      -- Reassemble the tail sum with the last block.
      simp [Fin.sum_univ_castSucc, add_comm]

/-- Helper for Theorem 6.30.22: a one-dimensional threshold block with nonnegative multiplier
reduces to the weighted threshold value. -/
lemma helperForTheorem_6_30_22_scalarThreshold_iInf_eq_weightedValue
    (a : EReal) (ha_bot : a ≠ (⊥ : EReal)) (ha_top : a < (⊤ : EReal))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨅ u : ℝ,
        (if a ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
          (((u * lam : ℝ) : EReal))) =
      (((lam : ℝ) : EReal) * a) := by
  -- Convert the finite threshold value `a` into the real coordinate `a.toReal`.
  have hcoe : (((a.toReal : ℝ) : EReal)) = a := by
    exact EReal.coe_toReal (x := a) ((lt_top_iff_ne_top).1 ha_top) ha_bot
  refine le_antisymm ?_ ?_
  · -- The witness `u = a.toReal` attains the threshold and therefore gives the upper bound.
    have hu : a ≤ (((a.toReal : ℝ) : EReal)) := by
      simpa [hcoe] using EReal.le_coe_toReal (x := a) ((lt_top_iff_ne_top).1 ha_top)
    refine le_trans (iInf_le _ a.toReal) ?_
    simp [hcoe, EReal.coe_mul, mul_comm, hu]
  · -- Any admissible `u` is at least `a.toReal`, and `lam ≥ 0` preserves that order.
    refine le_iInf ?_
    intro u
    by_cases hu : a ≤ ((u : ℝ) : EReal)
    · have htoReal_le : a.toReal ≤ u := by
        rw [← hcoe] at hu
        exact_mod_cast hu
      have hmul_real : lam * a.toReal ≤ u * lam := by
        nlinarith [hlam, htoReal_le]
      have hmul_ereal : (((lam * a.toReal : ℝ) : EReal)) ≤ (((u * lam : ℝ) : EReal)) := by
        exact_mod_cast hmul_real
      have hleft : (((lam : ℝ) : EReal) * a) = (((lam * a.toReal : ℝ) : EReal)) := by
        rw [← hcoe]
        simpa [EReal.coe_mul]
      rw [if_pos hu]
      simpa [hleft] using hmul_ereal
    · -- If the threshold fails, the corresponding block value is `⊤`.
      have htop : (⊤ : EReal) + (((u * lam : ℝ) : EReal)) = ⊤ := by
        simpa using EReal.top_add_coe (u * lam)
      rw [if_neg hu, htop]
      exact le_top

/-- Helper for Theorem 6.30.22: at a fixed primal point `x`, the enlarged feasibility indicator
splits into the sum of the independent coordinate indicators for the pairs `(uᵢ, xᵢ)`. -/
lemma helperForTheorem_6_30_22_feasibleIndicator_eq_sum_pairIndicators
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (xShift : Fin m → Fin n → ℝ) :
    indicatorFunction (enlargedPerturbationProgramFeasibleSet f
        ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } : EnlargedPerturbationParameter m n)) x =
      ∑ i : Fin m,
        (if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) := by
  classical
  let term : Fin m → EReal := fun i =>
    if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)
  by_cases hx : x ∈ enlargedPerturbationProgramFeasibleSet f
      ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } : EnlargedPerturbationParameter m n)
  · -- On the feasible branch every coordinate indicator is zero.
    have hterm_zero : ∀ i : Fin m, term i = 0 := by
      intro i
      simp [term, hx i]
    simp [indicatorFunction, hx, term, hterm_zero]
  · -- On the infeasible branch one bad coordinate forces the whole finite sum to be `⊤`.
    have hx' : ¬ ∀ i : Fin m, f i (x - xShift i) ≤ ((u i : ℝ) : EReal) := by
      simpa [enlargedPerturbationProgramFeasibleSet] using hx
    push_neg at hx'
    rcases hx' with ⟨i0, hi0⟩
    have htop_term : term i0 = (⊤ : EReal) := by
      simp [term, hi0]
    have hbot_term : ∀ j ∈ (Finset.univ : Finset (Fin m)), term j ≠ (⊥ : EReal) := by
      intro j hj
      by_cases hj' : f j (x - xShift j) ≤ ((u j : ℝ) : EReal)
      · simp [term, hj']
      · simp [term, hj']
    have hsum_top : ∑ i : Fin m, term i = (⊤ : EReal) := by
      exact sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
        (f := term) (i := i0) (by simp) htop_term hbot_term
    simp [indicatorFunction, hx, term, hsum_top]

/-- Helper for Theorem 6.30.22: a single constraint pair `(uᵢ, xᵢ)` collapses to the translated
weighted constraint term after minimizing over the scalar threshold variable. -/
lemma helperForTheorem_6_30_22_constraintPair_iInf_eq_weightedTranslated
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (x p : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hg_bot : ∀ y : Fin n → ℝ, g y ≠ (⊥ : EReal))
    (hg_top : ∀ y : Fin n → ℝ, g y < (⊤ : EReal)) :
    (⨅ q : ℝ × (Fin n → ℝ),
        (if g (x - q.2) ≤ ((q.1 : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
          (((q.1 * lam : ℝ) : EReal)) +
          (((q.2 ⬝ᵥ p : ℝ) : EReal))) =
      (⨅ y : Fin n → ℝ,
          (((lam : ℝ) : EReal) * g (x - y)) +
            (((y ⬝ᵥ p : ℝ) : EReal))) := by
  -- First separate the scalar threshold variable from the translated vector variable.
  have hNested :
      (⨅ q : ℝ × (Fin n → ℝ),
          (if g (x - q.2) ≤ ((q.1 : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((q.1 * lam : ℝ) : EReal)) +
            (((q.2 ⬝ᵥ p : ℝ) : EReal))) =
        (⨅ u : ℝ, ⨅ y : Fin n → ℝ,
          (if g (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((u * lam : ℝ) : EReal)) +
            (((y ⬝ᵥ p : ℝ) : EReal))) := by
    exact helperForTheorem_6_30_22_iInf_prod_eq_nested
      (H := fun u (y : Fin n → ℝ) =>
        (if g (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
          (((u * lam : ℝ) : EReal)) +
          (((y ⬝ᵥ p : ℝ) : EReal)))
  rw [hNested, iInf_comm]
  refine iInf_congr ?_
  intro y
  -- For fixed `y`, the dot-product term is a finite constant through the scalar infimum.
  have hsplit :
      (⨅ u : ℝ,
          (if g (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((u * lam : ℝ) : EReal)) +
            (((y ⬝ᵥ p : ℝ) : EReal))) =
        (⨅ u : ℝ,
          ((if g (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((u * lam : ℝ) : EReal))) +
            (((y ⬝ᵥ p : ℝ) : EReal))) := by
    refine iInf_congr ?_
    intro u
    simp [add_assoc]
  rw [hsplit, helperForTheorem_6_30_22_iInf_add_realConst
    (G := fun u : ℝ =>
      (if g (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
        (((u * lam : ℝ) : EReal)))
    (c := (y ⬝ᵥ p : ℝ))]
  -- The scalar threshold block now collapses to the weighted translated value.
  rw [helperForTheorem_6_30_22_scalarThreshold_iInf_eq_weightedValue
    (a := g (x - y))
    (ha_bot := hg_bot (x - y))
    (ha_top := hg_top (x - y))
    (lam := lam) (hlam := hlam)]

/-- Helper for Theorem 6.30.22: translating one affine block `y ↦ g (x - y) + ⟪y,p⟫` converts
its infimum into the expected linear term minus the Fenchel conjugate. -/
lemma helperForTheorem_6_30_22_translatedAffineBlock_iInf_eq_linear_minus_fenchel
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (x p : Fin n → ℝ) :
    (⨅ y : Fin n → ℝ, g (x - y) + (((y ⬝ᵥ p : ℝ) : EReal))) =
      (((x ⬝ᵥ p : ℝ) : EReal)) - fenchelConjugate n g p := by
  let e : (Fin n → ℝ) ≃ (Fin n → ℝ) :=
    { toFun := fun y => x - y
      invFun := fun z => x - z
      left_inv := by
        intro y
        ext i
        simp [sub_eq_add_neg]
      right_inv := by
        intro z
        ext i
        simp [sub_eq_add_neg] }
  have hReindex :
      (⨅ y : Fin n → ℝ, g (x - y) + (((y ⬝ᵥ p : ℝ) : EReal))) =
        (⨅ z : Fin n → ℝ, g z + ((((x - z) ⬝ᵥ p : ℝ) : EReal))) := by
    simpa [e] using
      (Equiv.iInf_congr e
        (f := fun y : Fin n → ℝ => g (x - y) + (((y ⬝ᵥ p : ℝ) : EReal)))
        (g := fun z : Fin n → ℝ => g z + ((((x - z) ⬝ᵥ p : ℝ) : EReal)))
        (fun y => by simp [e]))
  rw [hReindex]
  have hDot :
      (fun z : Fin n → ℝ => g z + ((((x - z) ⬝ᵥ p : ℝ) : EReal))) =
        (fun z : Fin n → ℝ =>
          (g z + (((z ⬝ᵥ (-p) : ℝ) : EReal))) + (((x ⬝ᵥ p : ℝ) : EReal))) := by
    funext z
    have hsub : ((x - z) ⬝ᵥ p : ℝ) = (z ⬝ᵥ (-p) : ℝ) + (x ⬝ᵥ p : ℝ) := by
      simp [dotProduct_sub, dotProduct_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hsub]
    simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
  rw [hDot, helperForTheorem_6_30_22_iInf_add_realConst
    (G := fun z : Fin n → ℝ => g z + (((z ⬝ᵥ (-p) : ℝ) : EReal)))
    (c := (x ⬝ᵥ p : ℝ))]
  rw [helperForTheorem_6_30_14_affineBlock_iInf_eq_neg_fenchelConjugate
    (f := g) (p := -p)]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 6.30.22: after the scalar thresholds have been removed, the remaining
family of translated affine blocks splits into the sum of the blockwise linear-minus-conjugate
terms. -/
lemma helperForTheorem_6_30_22_familyTranslatedAffine_iInf_eq_sum_linear_minus_fenchel
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (x : Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (lam : Fin m → ℝ) (hlam : ∀ i : Fin m, 0 ≤ lam i)
    (htop : ∀ i : Fin m, ∀ y : Fin n → ℝ, f i y < (⊤ : EReal)) :
    (⨅ y : Fin m → Fin n → ℝ,
        ∑ i : Fin m, ((((lam i : ℝ) : EReal) * f i (x - y i)) +
          (((y i ⬝ᵥ p i : ℝ) : EReal)))) =
      ∑ i : Fin m,
        ((((x ⬝ᵥ p i : ℝ) : EReal)) -
          fenchelConjugate n (fun z => (((lam i : ℝ) : EReal) * f i z)) (p i)) := by
  have hfinite :
      ∀ i : Fin m,
        ∃ y : Fin n → ℝ,
          ((((lam i : ℝ) : EReal) * f i (x - y)) +
            (((y ⬝ᵥ p i : ℝ) : EReal))) < (⊤ : EReal) := by
    -- Choosing `y = x` reduces each translated block to the finite value at `0`.
    intro i
    refine ⟨x, ?_⟩
    have hscaled_ne_top : (((lam i : ℝ) : EReal) * f i 0) ≠ (⊤ : EReal) := by
      by_cases hzero : lam i = 0
      · simp [hzero]
      · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hzero)
        exact (lt_top_iff_ne_top).1
          ((helperForTheorem_6_30_21_mul_lt_top_iff_of_pos
            (lam := lam i) hpos (f i 0)).2 (htop i 0))
    have hscaled_lt_top :
        ((((lam i : ℝ) : EReal) * f i 0) + (((x ⬝ᵥ p i : ℝ) : EReal))) < (⊤ : EReal) := by
      exact EReal.add_lt_top hscaled_ne_top (EReal.coe_ne_top _)
    simpa using hscaled_lt_top
  -- Split the family infimum into blockwise infima, then collapse each translated affine block.
  rw [helperForTheorem_6_30_22_family_iInf_sum_eq_sum_iInf_generic
    (g := fun i y =>
      ((((lam i : ℝ) : EReal) * f i (x - y)) + (((y ⬝ᵥ p i : ℝ) : EReal))))
    (hfinite := hfinite)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Each coordinate is exactly the one-block translated-affine formula.
  simpa using
    helperForTheorem_6_30_22_translatedAffineBlock_iInf_eq_linear_minus_fenchel
      (g := fun z => (((lam i : ℝ) : EReal) * f i z)) (x := x) (p := p i)

/-- Helper for Theorem 6.30.22: on the branch `u* ≥ 0`, the explicit dual objective is never
`⊤`, because each Fenchel-conjugate term is never `⊥`. -/
lemma helperForTheorem_6_30_22_dualObjective_ne_top_of_nonnegative
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    enlargedPerturbationDualObjective f0 f wStar ≠ (⊤ : EReal) := by
  let conjTail : Fin m → EReal := fun i =>
    fenchelConjugate n (fun x => (((wStar.uStar i : ℝ) : EReal) * f i x)) (wStar.xShiftStar i)
  have hproper0 : ProperConvexERealFunction (F := Fin n → ℝ) f0 :=
    helperForLemma_26_2_properConvexERealFunction hf0
  have hhead_ne_bot : fenchelConjugate n f0 wStar.x0Star ≠ (⊥ : EReal) := by
    -- Properness of `f₀` rules out `-∞` for its conjugate.
    exact helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
      (hf := hproper0.1) (xStar := wStar.x0Star)
  have hhead_ne_top : -fenchelConjugate n f0 wStar.x0Star ≠ (⊤ : EReal) := by
    simpa [EReal.neg_eq_top_iff] using hhead_ne_bot
  have htail_ne_bot : ∑ i : Fin m, conjTail i ≠ (⊥ : EReal) := by
    -- Every scaled constraint block is proper on the nonnegative branch, so its conjugate is not
    -- `⊥`; a finite sum of such terms stays away from `⊥`.
    refine sum_ne_bot_of_ne_bot (s := Finset.univ) (f := conjTail) ?_
    intro i hi
    have hproperFi : ProperConvexERealFunction (F := Fin n → ℝ) (f i) :=
      helperForLemma_26_2_properConvexERealFunction (hf i)
    have hscaledOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun x => (((wStar.uStar i : ℝ) : EReal) * f i x)) := by
      simpa using
        helperForTheorem_6_30_21_properConvexFunctionOn_univ_mul_of_nonneg
          (f := f i) (hf := hproperFi) (hlam := hnonneg i)
    have hscaled : ProperConvexERealFunction (F := Fin n → ℝ)
        (fun x => (((wStar.uStar i : ℝ) : EReal) * f i x)) :=
      helperForLemma_26_2_properConvexERealFunction hscaledOn
    exact helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
      (hf := hscaled.1) (xStar := wStar.xShiftStar i)
  have htail_ne_top : -(∑ i : Fin m, conjTail i) ≠ (⊤ : EReal) := by
    simpa [EReal.neg_eq_top_iff] using htail_ne_bot
  -- Reinterpret the explicit dual objective as a sum of two non-`⊤` terms.
  rw [enlargedPerturbationDualObjective, sub_eq_add_neg]
  exact EReal.add_ne_top hhead_ne_top htail_ne_top

/-- Helper for Theorem 6.30.22: a nonzero linear form plus any constant different from `⊤`
still has infimum `-∞`. -/
lemma helperForTheorem_6_30_22_sInf_linear_plus_nonTopConst_eq_bot_of_ne_zero
    {n : ℕ} (b : Fin n → ℝ) (c : EReal)
    (hb : b ≠ 0) (hc : c ≠ (⊤ : EReal)) :
    sInf (Set.range fun x : Fin n → ℝ => (((x ⬝ᵥ b : ℝ) : EReal) + c)) = (⊥ : EReal) := by
  rw [sInf_range]
  by_cases hbot : c = (⊥ : EReal)
  · -- If the additive constant is already `⊥`, every ranged value is `⊥`.
    subst hbot
    simp
  · have hcoe : (((c.toReal : ℝ) : EReal)) = c := by
      exact EReal.coe_toReal (x := c) hc hbot
    -- Otherwise rewrite the constant as a real and reduce to the existing affine-ray lemma.
    calc
      (⨅ x : Fin n → ℝ, (((x ⬝ᵥ b : ℝ) : EReal) + c)) =
          (⨅ x : Fin n → ℝ, ((((x ⬝ᵥ b : ℝ) + c.toReal : ℝ) : EReal))) := by
            refine iInf_congr ?_
            intro x
            rw [← hcoe]
            simpa [EReal.coe_add]
      _ = (⊥ : EReal) := by
            simpa [sInf_range] using
              helperForTheorem_6_30_22_sInf_linear_term_eq_bot_of_ne_zero_with_realConst
                (b := b) (r := c.toReal) hb

/-- Helper for Theorem 6.30.22: coercing a finite real sum into `EReal` is the same as summing
the termwise `EReal` coercions. -/
lemma helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) :
    (((s.sum r : ℝ)) : EReal) = s.sum (fun i => (((r i : ℝ) : EReal))) := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is preserved by the `EReal` coercion.
      simp
  | @insert i s hi ih =>
      -- The insert step follows from `EReal.coe_add`.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

/-- Helper for Theorem 6.30.22: at fixed `x`, the `(u, xShift)` integrand can be normalized
pointwise into a finite sum of independent coordinate blocks. -/
lemma helperForTheorem_6_30_22_uBlock_pointwise_sum_normal_form
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (xShift : Fin m → Fin n → ℝ)
    (wStar : EnlargedPerturbationDualParameter m n) :
    indicatorFunction (enlargedPerturbationProgramFeasibleSet f
        ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
          EnlargedPerturbationParameter m n)) x +
      (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
      ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) =
    ∑ i : Fin m,
      ((if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
        (((u i * wStar.uStar i : ℝ) : EReal)) +
        (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) := by
  -- Rewrite the feasibility indicator as the finite sum of coordinate indicators.
  rw [helperForTheorem_6_30_22_feasibleIndicator_eq_sum_pairIndicators
    (f := f) (x := x) (u := u) (xShift := xShift)]
  have hdot :
      (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) =
        ∑ i : Fin m, (((u i * wStar.uStar i : ℝ) : EReal)) := by
    -- Expand the dot product and commute the `EReal` coercion with the finite sum.
    rw [dotProduct]
    simpa using
      helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe
        (s := Finset.univ) (r := fun i : Fin m => u i * wStar.uStar i)
  rw [hdot]
  -- Collect the three finite sums into one coordinatewise block sum.
  calc
    (∑ i : Fin m,
        (if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal))) +
        ∑ i : Fin m, (((u i * wStar.uStar i : ℝ) : EReal)) +
        ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) =
      (∑ i : Fin m,
          ((if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((u i * wStar.uStar i : ℝ) : EReal)))) +
        ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) := by
          rw [← Finset.sum_add_distrib]
    _ =
      ∑ i : Fin m,
        (((if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
            (((u i * wStar.uStar i : ℝ) : EReal))) +
          (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) := by
            rw [← Finset.sum_add_distrib]
    _ =
      ∑ i : Fin m,
        ((if f i (x - xShift i) ≤ ((u i : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
          (((u i * wStar.uStar i : ℝ) : EReal)) +
          (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [add_assoc]

/-- Helper for Theorem 6.30.22: the nested infimum over scalar thresholds and translated
coordinates can be reindexed as a single family of coordinate pairs. -/
lemma helperForTheorem_6_30_22_uBlock_nested_iInf_to_familyPairs_staged
    {m n : ℕ}
    (H : Fin m → ℝ → (Fin n → ℝ) → EReal) :
    (⨅ u : Fin m → ℝ, ⨅ xShift : Fin m → Fin n → ℝ,
        ∑ i : Fin m, H i (u i) (xShift i)) =
      (⨅ z : Fin m → ℝ × (Fin n → ℝ),
          ∑ i : Fin m, H i (z i).1 (z i).2) := by
  calc
    (⨅ u : Fin m → ℝ, ⨅ xShift : Fin m → Fin n → ℝ,
        ∑ i : Fin m, H i (u i) (xShift i)) =
      (⨅ p : (Fin m → ℝ) × (Fin m → Fin n → ℝ),
          ∑ i : Fin m, H i (p.1 i) (p.2 i)) := by
            -- First package the two global families as an infimum over their product.
            simpa using
              (helperForTheorem_6_30_22_iInf_prod_eq_nested
                (H := fun (u : Fin m → ℝ) (xShift : Fin m → Fin n → ℝ) =>
                  ∑ i : Fin m, H i (u i) (xShift i))).symm
    _ =
      (⨅ z : Fin m → ℝ × (Fin n → ℝ),
          ∑ i : Fin m, H i (z i).1 (z i).2) := by
            -- Then reindex the product family as a single family of pairs.
            exact helperForTheorem_6_30_22_pairFamily_iInf_eq_familyPairs (H := H)

/-- Helper for Theorem 6.30.22: at a fixed primal point `x`, the whole `(u, xShift)` block of
the enlarged adjoint collapses to the translated weighted-constraint family. -/
lemma helperForTheorem_6_30_22_uBlock_iInf_eq_translatedConstraintFamily
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    (x : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    (⨅ u : Fin m → ℝ,
        ⨅ xShift : Fin m → Fin n → ℝ,
          indicatorFunction (enlargedPerturbationProgramFeasibleSet f
              ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
                EnlargedPerturbationParameter m n)) x +
            (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
            ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) =
      (⨅ y : Fin m → Fin n → ℝ,
          ∑ i : Fin m,
            ((((wStar.uStar i : ℝ) : EReal) * f i (x - y i)) +
              (((y i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)))) := by
  let block : Fin m → ℝ → (Fin n → ℝ) → EReal := fun i u y =>
    (if f i (x - y) ≤ ((u : ℝ) : EReal) then (0 : EReal) else (⊤ : EReal)) +
      (((u * wStar.uStar i : ℝ) : EReal)) +
      (((y ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))
  let translated : Fin m → (Fin n → ℝ) → EReal := fun i y =>
    ((((wStar.uStar i : ℝ) : EReal) * f i (x - y)) +
      (((y ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)))
  have hfinite_block :
      ∀ i : Fin m, ∃ q : ℝ × (Fin n → ℝ), block i q.1 q.2 < (⊤ : EReal) := by
    intro i
    have hxi_mem :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      rw [hdom i]
      simp
    have hxi_top : f i x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxi_mem
    refine ⟨(((f i x).toReal), (0 : Fin n → ℝ)), ?_⟩
    have hle :
        f i x ≤ ((((f i x).toReal : ℝ) : EReal)) := by
      simpa using
        EReal.le_coe_toReal (x := f i x) ((lt_top_iff_ne_top).1 hxi_top)
    have hterm :
        block i (f i x).toReal (0 : Fin n → ℝ) =
          ((((f i x).toReal * wStar.uStar i : ℝ) : EReal)) := by
      simp [block, hle]
    rw [hterm]
    exact (lt_top_iff_ne_top).2 (EReal.coe_ne_top _)
  have hfinite_translated :
      ∀ i : Fin m, ∃ y : Fin n → ℝ, translated i y < (⊤ : EReal) := by
    intro i
    have hzero_mem :
        (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      rw [hdom i]
      simp
    have hzero_top : f i 0 < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hzero_mem
    refine ⟨x, ?_⟩
    have hscaled_ne_top :
        (((wStar.uStar i : ℝ) : EReal) * f i 0) ≠ (⊤ : EReal) := by
      by_cases hzero : wStar.uStar i = 0
      · simp [hzero]
      · have hpos : 0 < wStar.uStar i := lt_of_le_of_ne (hnonneg i) (Ne.symm hzero)
        exact (lt_top_iff_ne_top).1
          ((helperForTheorem_6_30_21_mul_lt_top_iff_of_pos
            (lam := wStar.uStar i) hpos (f i 0)).2 hzero_top)
    have hsum_top :
        ((((wStar.uStar i : ℝ) : EReal) * f i 0) +
            (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) < (⊤ : EReal) := by
      exact EReal.add_lt_top hscaled_ne_top (EReal.coe_ne_top _)
    simpa [translated] using hsum_top
  -- First normalize the `(u, xShift)` integrand pointwise into a sum of coordinate blocks.
  calc
    (⨅ u : Fin m → ℝ,
        ⨅ xShift : Fin m → Fin n → ℝ,
          indicatorFunction (enlargedPerturbationProgramFeasibleSet f
              ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
                EnlargedPerturbationParameter m n)) x +
            (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
            ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) =
      (⨅ u : Fin m → ℝ,
        ⨅ xShift : Fin m → Fin n → ℝ,
          ∑ i : Fin m, block i (u i) (xShift i)) := by
            refine iInf_congr ?_
            intro u
            refine iInf_congr ?_
            intro xShift
            simpa [block] using
              helperForTheorem_6_30_22_uBlock_pointwise_sum_normal_form
                (f := f) (x := x) (u := u) (xShift := xShift) (wStar := wStar)
    -- Reindex the nested infimum as a single family of coordinate pairs.
    _ =
      (⨅ z : Fin m → ℝ × (Fin n → ℝ),
          ∑ i : Fin m, block i (z i).1 (z i).2) := by
            simpa [block] using
              helperForTheorem_6_30_22_uBlock_nested_iInf_to_familyPairs_staged
                (m := m) (n := n) (H := block)
    -- Split the family infimum into its independent coordinate blocks.
    _ =
      ∑ i : Fin m, (⨅ q : ℝ × (Fin n → ℝ), block i q.1 q.2) := by
            let gPair : Fin m → (ℝ × (Fin n → ℝ)) → EReal := fun i q => block i q.1 q.2
            have hgPair :
                (⨅ z : Fin m → ℝ × (Fin n → ℝ), ∑ i : Fin m, block i (z i).1 (z i).2) =
                  (⨅ z : Fin m → ℝ × (Fin n → ℝ), ∑ i : Fin m, gPair i (z i)) := by
              simp [gPair]
            rw [hgPair]
            simpa [gPair] using
              helperForTheorem_6_30_22_family_iInf_sum_eq_sum_iInf_generic
                (g := gPair) (hfinite := hfinite_block)
    -- Collapse each coordinate block by eliminating the scalar threshold variable.
    _ =
      ∑ i : Fin m, (⨅ y : Fin n → ℝ, translated i y) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hproperFi : ProperConvexERealFunction (F := Fin n → ℝ) (f i) :=
              helperForLemma_26_2_properConvexERealFunction (hf i)
            have hbotFi : ∀ y : Fin n → ℝ, f i y ≠ (⊥ : EReal) := by
              intro y
              exact hproperFi.1.1 y
            have htopFi : ∀ y : Fin n → ℝ, f i y < (⊤ : EReal) := by
              intro y
              have hy_mem :
                  y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
                rw [hdom i]
                simp
              simpa [effectiveDomain_eq] using hy_mem
            -- Each coordinate uses the previously isolated one-block threshold formula.
            simpa [block, translated] using
              helperForTheorem_6_30_22_constraintPair_iInf_eq_weightedTranslated
                (g := f i) (x := x) (p := wStar.xShiftStar i)
                (lam := wStar.uStar i) (hlam := hnonneg i)
                (hg_bot := hbotFi) (hg_top := htopFi)
    -- Reassemble the blockwise infima as the family infimum of the translated constraints.
    _ =
      (⨅ y : Fin m → Fin n → ℝ, ∑ i : Fin m, translated i (y i)) := by
            symm
            simpa using
              helperForTheorem_6_30_22_family_iInf_sum_eq_sum_iInf_generic
                (g := translated) (hfinite := hfinite_translated)
    _ =
      (⨅ y : Fin m → Fin n → ℝ,
          ∑ i : Fin m,
            ((((wStar.uStar i : ℝ) : EReal) * f i (x - y i)) +
              (((y i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)))) := by
            simp [translated]

/-- Helper for Theorem 6.30.22: the linear terms coming from `x₀*`, the translated coordinates,
and `-x*` collect into the single coefficient
`x₀* + ⋯ + x_m* - x*`. -/
lemma helperForTheorem_6_30_22_translationLinearTerms_collect
    {m n : ℕ} (x xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n) :
    (((x ⬝ᵥ wStar.x0Star : ℝ) : EReal)) +
      ∑ i : Fin m, (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) +
      (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) =
    (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) := by
  have hsum :
      (∑ i : Fin m, (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) =
        ((((∑ i : Fin m, (x ⬝ᵥ wStar.xShiftStar i : ℝ) : ℝ)) : ℝ) : EReal) := by
    have hsumSet :
        ∀ s : Finset (Fin m),
          s.sum (fun i => (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) =
            (((s.sum (fun i => (x ⬝ᵥ wStar.xShiftStar i : ℝ)) : ℝ) : EReal)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro i s hi hs
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hs]
        simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
    simpa using hsumSet Finset.univ
  have hsumDot :
      (∑ i : Fin m, (x ⬝ᵥ wStar.xShiftStar i : ℝ)) =
        (x ⬝ᵥ ∑ i : Fin m, wStar.xShiftStar i : ℝ) := by
    simpa using (dotProduct_sum x Finset.univ wStar.xShiftStar).symm
  rw [hsum]
  have hreal :
      (x ⬝ᵥ wStar.x0Star : ℝ) + (∑ i : Fin m, (x ⬝ᵥ wStar.xShiftStar i : ℝ)) +
          (-(x ⬝ᵥ xStar : ℝ)) =
        (x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) := by
    -- Expand the dot products and collect the linear coefficients in `ℝ`.
    rw [hsumDot]
    simp [enlargedPerturbationDualTranslationSum, dotProduct_add, dotProduct_sub,
      Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Convert the collected real identity back into `EReal`.
  rw [show
      (((x ⬝ᵥ wStar.x0Star : ℝ) : EReal) +
          ((((∑ i : Fin m, (x ⬝ᵥ wStar.xShiftStar i : ℝ) : ℝ)) : ℝ) : EReal)) +
        (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) =
      ((((x ⬝ᵥ wStar.x0Star : ℝ) + (∑ i : Fin m, (x ⬝ᵥ wStar.xShiftStar i : ℝ)) +
          (-(x ⬝ᵥ xStar : ℝ)) : ℝ)) : EReal) by
    simp [EReal.coe_add, add_assoc]]
  simp [hreal]


end Section30
end Chap06
