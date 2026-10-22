/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- Helper for Proposition 4.46: the beta-parameter `α / (1 - α)` is positive for `α ∈ (0, 1)`. -/
private lemma beta_pos_of_mem_Ioo {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    0 < α / (1 - α) := by
  exact div_pos hα.1 (sub_pos.mpr hα.2)

/-- Helper for Proposition 4.46: the normalized beta-parameter recovers the original averaging
constant. -/
private lemma beta_div_one_add_beta_eq_self {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (α / (1 - α)) / (1 + α / (1 - α)) = α := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_of_lt hα.2).symm
  field_simp [h1]
  ring

/-- Helper for Proposition 4.46: the composition constant from Proposition 4.44 matches the
beta-sum normalization. -/
private lemma compositionAveragingConstant_beta {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    compositionAveragingConstant (β₁ / (1 + β₁)) (β₂ / (1 + β₂)) =
      (β₁ + β₂) / (1 + (β₁ + β₂)) := by
  have h1 : 1 + β₁ ≠ 0 := ne_of_gt (by linarith : 0 < 1 + β₁)
  have h2 : 1 + β₂ ≠ 0 := ne_of_gt (by linarith : 0 < 1 + β₂)
  have hsum : 1 + (β₁ + β₂) ≠ 0 := ne_of_gt (by linarith : 0 < 1 + (β₁ + β₂))
  have hnum :
      β₁ / (1 + β₁) + β₂ / (1 + β₂) - 2 * (β₁ / (1 + β₁)) * (β₂ / (1 + β₂)) =
        (β₁ + β₂) / ((1 + β₁) * (1 + β₂)) := by
    field_simp [h1, h2]
    ring
  have hden :
      1 - (β₁ / (1 + β₁)) * (β₂ / (1 + β₂)) =
        (1 + (β₁ + β₂)) / ((1 + β₁) * (1 + β₂)) := by
    field_simp [h1, h2, hsum]
    ring
  rw [compositionAveragingConstant, hnum, hden]
  field_simp [h1, h2, hsum]

/-- Helper for Proposition 4.46: the composition of two beta-averaged maps is
`(β₁ + β₂) / (1 + β₁ + β₂)`-averaged. -/
private theorem averagedWith_comp_beta {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    {T₁ T₂ : D → D}
    (hT₁ : AveragedWith (β₁ / (1 + β₁)) (fun x : D ↦ ((T₁ x : D) : H)))
    (hT₂ : AveragedWith (β₂ / (1 + β₂)) (fun x : D ↦ ((T₂ x : D) : H))) :
    AveragedWith ((β₁ + β₂) / (1 + (β₁ + β₂))) (fun x : D ↦ ((T₁ (T₂ x) : D) : H)) := by
  simpa [compositionAveragingConstant_beta hβ₁ hβ₂] using averagedWith_comp hT₁ hT₂

/-- Helper for Proposition 4.46: folding a list of endomorphisms against composition with a base
map is the same as first folding from `id` and then composing with that base map. -/
private lemma foldr_comp_eq_comp {α : Type*} (l : List (α → α)) (g : α → α) :
    l.foldr (· ∘ ·) g = l.foldr (· ∘ ·) id ∘ g := by
  induction l with
  | nil =>
      rfl
  | cons f l ih =>
      simp [ih, Function.comp_assoc]

/-- Helper for Proposition 4.46: the ordered fold over `Fin (n + 1)` splits into the prefix fold
composed with the last map. -/
private lemma foldr_ofFn_succ_eq_prefix_comp_last {α : Type*} (n : ℕ) (f : Fin (n + 1) → α → α) :
    (List.ofFn f).foldr (· ∘ ·) id =
      ((List.ofFn (fun i : Fin n ↦ f i.castSucc)).foldr (· ∘ ·) id) ∘ f (Fin.last n) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append, List.foldr]
  simpa using foldr_comp_eq_comp (List.ofFn fun i : Fin n ↦ f i.castSucc) (f (Fin.last n))

/-- Helper for Proposition 4.46: the beta-sum over `Fin (n + 1)` splits into the prefix sum plus
the last beta-term. -/
private lemma sum_beta_castSucc_last (n : ℕ) (α : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), α i / (1 - α i)) =
      (∑ i : Fin n, α i.castSucc / (1 - α i.castSucc)) +
        α (Fin.last n) / (1 - α (Fin.last n)) := by
  simpa using
    (Fin.sum_univ_castSucc (fun i : Fin (n + 1) ↦ α i / (1 - α i)))

/-- Helper for Proposition 4.46: the canonical finite ordered composition agrees with the
corresponding `List.ofFn` fold. -/
private lemma finiteComposition_eq_foldr_ofFn {α : Type*} :
    {m : ℕ} → (T : Fin m → α → α) → finiteComposition T = (List.ofFn T).foldr (· ∘ ·) id
  | 0, _ => rfl
  | _ + 1, T => by
      rw [finiteComposition_succ, List.ofFn_succ, List.foldr_cons, finiteComposition_eq_foldr_ofFn]

/-- Helper for Proposition 4.46: the ordered composition of a nonempty finite family of averaged
maps is averaged with the beta-sum parameter. -/
private theorem averagedWith_compose_fin_aux
    (n : ℕ) (α : Fin (n + 1) → ℝ) (T : Fin (n + 1) → D → D)
    (hT : ∀ i, AveragedWith (α i) (fun x : D ↦ ((T i x : D) : H))) :
    AveragedWith
      (((∑ i : Fin (n + 1), α i / (1 - α i)) / (1 + ∑ i : Fin (n + 1), α i / (1 - α i))) : ℝ)
      (fun x : D ↦ (((List.ofFn T).foldr (· ∘ ·) id) x : H)) := by
  induction n with
  | zero =>
      simpa [beta_div_one_add_beta_eq_self (hT 0).mem_Ioo] using hT 0
  | succ n ih =>
      have hprefix :
          AveragedWith
            (((∑ i : Fin (n + 1), α i.castSucc / (1 - α i.castSucc)) /
                (1 + ∑ i : Fin (n + 1), α i.castSucc / (1 - α i.castSucc))) : ℝ)
            (fun x : D ↦
              (((List.ofFn (fun i : Fin (n + 1) ↦ T i.castSucc)).foldr (· ∘ ·) id) x : H)) := by
        exact ih (fun i : Fin (n + 1) ↦ α i.castSucc) (fun i : Fin (n + 1) ↦ T i.castSucc)
          (fun i ↦ hT i.castSucc)
      have hprefixPos :
          0 < ∑ i : Fin (n + 1), α i.castSucc / (1 - α i.castSucc) := by
        let f : Fin (n + 1) → ℝ := fun i ↦ α i.castSucc / (1 - α i.castSucc)
        have hsumuniv : 0 < ∑ i : Fin (n + 1), f i := by
          exact Finset.sum_pos
            (fun i _ ↦ beta_pos_of_mem_Ioo (hT i.castSucc).mem_Ioo)
            Finset.univ_nonempty
        simpa [f] using hsumuniv
      have hlast :
          AveragedWith
            ((α (Fin.last (n + 1)) / (1 - α (Fin.last (n + 1)))) /
                (1 + α (Fin.last (n + 1)) / (1 - α (Fin.last (n + 1)))) : ℝ)
            (fun x : D ↦ ((T (Fin.last (n + 1)) x : D) : H)) := by
        simpa [beta_div_one_add_beta_eq_self (hT (Fin.last (n + 1))).mem_Ioo] using
          hT (Fin.last (n + 1))
      have hcomp :=
        averagedWith_comp_beta hprefixPos
          (beta_pos_of_mem_Ioo (hT (Fin.last (n + 1))).mem_Ioo) hprefix hlast
      convert hcomp using 1
      · rw [sum_beta_castSucc_last]
      · ext x
        rw [foldr_ofFn_succ_eq_prefix_comp_last]
        rfl

/-- Helper for Proposition 4.46: `B / (1 + B)` can be rewritten as `1 / (1 + B⁻¹)` for `B > 0`. -/
private lemma beta_sum_div_eq_inv_one_add_inv {B : ℝ} (hB : 0 < B) :
    B / (1 + B) = 1 / (1 + B⁻¹) := by
  have hB0 : B ≠ 0 := ne_of_gt hB
  have h1 : 1 + B ≠ 0 := ne_of_gt (by linarith : 0 < 1 + B)
  have h2 : 1 + B⁻¹ ≠ 0 := by
    have : 0 < 1 + B⁻¹ := by positivity
    exact ne_of_gt this
  field_simp [hB0, h1, h2]
  ring

-- Proof sketch: use the beta-invariant `β i = α i / (1 - α i)`, prove by induction that the
-- ordered fold is `(∑ i, β i) / (1 + ∑ i, β i)`-averaged, and normalize this parameter to the
-- textbook form `1 / (1 + (∑ i, β i)⁻¹)` at the end.
/-- Proposition 4.46: if `D` is nonempty, `m ≥ 2`, and each self-map `T i : D → D` is
`α i`-averaged, then the increasing-order composition `T 0 ∘ T 1 ∘ ... ∘ T (m - 1)` is
`1 / (1 + (∑ i, α i / (1 - α i))⁻¹)`-averaged. -/
theorem averagedWith_compose_fin
    {m : ℕ} (_hm : 2 ≤ m) (_hD : D.Nonempty) (α : Fin m → ℝ) (T : Fin m → D → D)
    (hT : ∀ i, AveragedWith (α i) (fun x : D ↦ ((T i x : D) : H))) :
    AveragedWith (1 / (1 + (∑ i : Fin m, α i / (1 - α i))⁻¹) : ℝ)
      (fun x : D ↦ ((finiteComposition T : D → D) x : H)) := by
  cases m with
  | zero =>
      cases _hm
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ k =>
          have haux := averagedWith_compose_fin_aux (k + 1) α T hT
          have hsumPos : 0 < ∑ i : Fin (Nat.succ (Nat.succ k)), α i / (1 - α i) := by
            let f : Fin (Nat.succ (Nat.succ k)) → ℝ := fun i ↦ α i / (1 - α i)
            have hsumuniv : 0 < ∑ i : Fin (Nat.succ (Nat.succ k)), f i := by
              exact Finset.sum_pos
                (fun i _ ↦ beta_pos_of_mem_Ioo (hT i).mem_Ioo)
                Finset.univ_nonempty
            simpa [f] using hsumuniv
          simpa [beta_sum_div_eq_inv_one_add_inv hsumPos, finiteComposition_eq_foldr_ofFn] using
            haux

end
