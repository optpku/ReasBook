/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Example_5_3_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: `(i) → (ii)` comes from Example 5.3.2 and Proposition 5.4(1), since every
-- Picard orbit of a nonexpansive self-map is Fejér monotone with respect to the ambient
-- fixed-point set.
-- `(ii) → (iii)` is immediate. For `(iii) → (i)`, apply Proposition 11.18(6) to the bounded
-- orbit to see that its asymptotic center relative to `C` belongs to
-- `Subtype.val '' fixedPoints T`, hence `Function.fixedPoints T` is nonempty.
/-- Corollary 11.19: for a nonexpansive self-map of a nonempty closed convex subset of a real
Hilbert space, nonemptiness of the fixed-point set, boundedness of every Picard orbit, and
boundedness of some Picard orbit are equivalent. -/
theorem fixedPoints_nonempty_bounded_picard_orbits_tfae_of_nonexpansive
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : C → C} (hT : LipschitzWith 1 T) :
    List.TFAE [
      (Function.fixedPoints T).Nonempty,
      ∀ z₀ : C, Bornology.IsBounded (Set.range fun n ↦ ((T^[n]) z₀ : H)),
      ∃ z₀ : C, Bornology.IsBounded (Set.range fun n ↦ ((T^[n]) z₀ : H))
    ] := by
  tfae_have 1 → 2 := by
    intro hFix z₀
    have hquasi : IsQuasinonexpansiveOn (fun x : C ↦ (T x : H)) := by
      intro x y hy
      have hxy : ‖(T x : H) - (T y : H)‖ ≤ ‖(x : H) - y‖ := by
        simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT.dist_le_mul x y
      simpa [hy] using hxy
    have hfejer :
        FejerMonotone (Subtype.val '' Function.fixedPoints T) (fun n ↦ ((T^[n]) z₀ : H)) :=
      quasinonexpansive_iterates_fejer_monotone T hquasi z₀
    have hFix_image : (Subtype.val '' Function.fixedPoints T).Nonempty := by
      simpa using Set.Nonempty.image Subtype.val hFix
    exact hfejer.isBounded hFix_image
  tfae_have 2 → 3 := by
    intro hbounded
    rcases hC_nonempty with ⟨z₀, hz₀⟩
    exact ⟨⟨z₀, hz₀⟩, hbounded ⟨z₀, hz₀⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨z₀, hz₀_bdd⟩
    let zₙ : ℕ → H := fun n ↦ ((T^[n]) z₀ : H)
    have hzₙ_mem : ∀ n, zₙ n ∈ C := fun n ↦ ((T^[n]) z₀).2
    have horbit : ∀ n, zₙ (n + 1) = T ⟨zₙ n, hzₙ_mem n⟩ := by
      intro n
      simp [zₙ, Function.iterate_succ_apply']
    have hcenter :
        asymptoticCenter zₙ C hz₀_bdd hC_nonempty hC_closed hC_convex ∈
          Subtype.val '' Function.fixedPoints T :=
      asymptoticCenter_mem_fixedPoints_of_orbit hz₀_bdd hC_nonempty hC_closed hC_convex hT
        hzₙ_mem horbit
    rcases hcenter with ⟨z, hz, _⟩
    exact ⟨z, hz⟩
  tfae_finish

end
