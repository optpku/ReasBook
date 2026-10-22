/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {p : ℕ} {E : Fin p → Type u}

local notation "BlockSpace" => PiLp (2 : ENNReal) E

/- Definition 14.1 is `source-facing`: the source item names the mixed inner states `x^{k,i}`
attached to an explicit outer iterate sequence `x^k`.

Domain sampling shows the following owner split.
- `core/canonical`: `alternating_minimization_partial_state` from Algorithm 14.1 is the chapter
  owner for one Gauss-Seidel block replacement on the coordinate family;
- `bridge/view`: Chapter 11's `𝒰[i]` and its coordinate lemmas are the canonical additive
  singleton presentation of a one-block update in `PiLp 2 E`;
- `source-facing`: this file keeps the textbook family `x^{k,i}` itself, obtained by adjoining the
  initial state `x^k` to the successive canonical one-block replacements.

Accordingly, the primitive data here are only the iterate family `x`. The successor auxiliary
states are derived from the owner `alternating_minimization_partial_state`, while the additive
update formula is stated through the existing Chapter 11 block embedding API. -/

/-- Definition 14.1: for an outer iterate sequence `x^k` in the block product `PiLp 2 E`, the
auxiliary state `x^{k,i}` uses the new iterate `x^(k+1)` in blocks with index `< i` and the old
iterate `x^k` in the remaining blocks. -/
def alternating_minimization_auxiliary_iterate
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin (p + 1)) : BlockSpace :=
  WithLp.toLp 2 (fun j ↦ if j.castSucc < i then x (k + 1) j else x k j)

/-- The successor auxiliary state is the canonical Algorithm 14.1 mixed block state with the
active block set to the next iterate value. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_succ
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin p) :
    alternating_minimization_auxiliary_iterate x k i.succ =
      WithLp.toLp 2
        (alternating_minimization_partial_state
          (fun j ↦ x k j)
          (fun j ↦ x (k + 1) j)
          i
          (x (k + 1) i)) := by
  ext j
  by_cases hji : j < i
  · have hcut : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.mpr (le_of_lt hji)
    change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
      if j < i then (x (k + 1)).ofLp j else
        Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) j
    rw [if_pos hcut, if_pos hji]
  · by_cases h : j = i
    · subst j
      change (if i.castSucc < i.succ then (x (k + 1)).ofLp i else (x k).ofLp i) =
        if i < i then (x (k + 1)).ofLp i else
          Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) i
      simp
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm h)
      have hcut : ¬ j.castSucc < i.succ := by
        intro h'
        exact not_lt_of_ge (Fin.castSucc_lt_succ_iff.mp h') hij
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        if j < i then (x (k + 1)).ofLp j else
          Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) j
      rw [if_neg hcut, if_neg hji]
      simp [Function.update, h]

/-- The coordinates of `x^{k,i}` agree with the textbook mixed-state rule. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_apply
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin (p + 1)) (j : Fin p) :
    alternating_minimization_auxiliary_iterate x k i j =
      if j.castSucc < i then x (k + 1) j else x k j :=
  rfl

/-- The initial auxiliary state is the current outer iterate `x^k`. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_zero
    (x : ℕ → BlockSpace) (k : ℕ) :
    alternating_minimization_auxiliary_iterate x k 0 = x k := by
  ext j
  rw [alternating_minimization_auxiliary_iterate_apply]
  simp

/-- The terminal auxiliary state is the next outer iterate `x^(k+1)`. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_last
    (x : ℕ → BlockSpace) (k : ℕ) :
    alternating_minimization_auxiliary_iterate x k (Fin.last p) = x (k + 1) := by
  ext j
  rw [alternating_minimization_auxiliary_iterate_apply]
  simp [Fin.castSucc_lt_last]

section

variable [∀ i, NormedAddCommGroup (E i)]

recall PiLp.single

/-- Passing from `x^{k,i-1}` to `x^{k,i}` updates exactly block `i` by the Chapter 11 block
embedding `𝒰[i]`. This is the Chapter 14 block-update surface
`x^{k,i} = x^{k,i-1} + 𝒰[i] (x_i^(k+1) - x_i^k)`. -/
theorem alternating_minimization_auxiliary_iterate_succ_eq_add_single
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin p) :
    alternating_minimization_auxiliary_iterate x k i.succ =
      alternating_minimization_auxiliary_iterate x k i.castSucc +
        𝒰[i] (x (k + 1) i - x k i) := by
  ext j
  by_cases h : j = i
  · subst j
    change (if i.castSucc < i.succ then (x (k + 1)).ofLp i else (x k).ofLp i) =
      (if i.castSucc < i.castSucc then (x (k + 1)).ofLp i else (x k).ofLp i) +
        (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) i
    simp [block_coordinate_embedding_apply_same]
  · by_cases hji : j < i
    · have hsucc : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.mpr (le_of_lt hji)
      have hpred : j.castSucc < i.castSucc := by simpa using hji
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        (if j.castSucc < i.castSucc then (x (k + 1)).ofLp j else (x k).ofLp j) +
          (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) j
      rw [if_pos hsucc, if_pos hpred]
      simp [h]
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm h)
      have hsucc : ¬ j.castSucc < i.succ := by
        intro h'
        exact not_lt_of_ge (Fin.castSucc_lt_succ_iff.mp h') hij
      have hpred : ¬ j.castSucc < i.castSucc := by
        intro h'
        exact hji (by simpa using h')
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        (if j.castSucc < i.castSucc then (x (k + 1)).ofLp j else (x k).ofLp j) +
          (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) j
      rw [if_neg hsucc, if_neg hpred]
      simp [h]

end

end
