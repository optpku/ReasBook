/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u} [Fintype E]

private theorem sum_union_eq_sum_diff_add_sum (A0 A1 : Set E) (f : E → ℝ) :
    let A : Set E := A0 ∪ A1
    (∑ x : A, f x) = (∑ x : ((A0 \ A1 : Set E)), f x) + ∑ x : A1, f x := by
  set A : Set E := A0 ∪ A1
  have hdisj : Disjoint (A0 \ A1 : Set E) A1 := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    exact hx0.2 hx1
  have hunion : ((A0 \ A1 : Set E) ∪ A1) = A := by
    ext x
    simp [A]
  let e : ((A0 \ A1 : Set E) ⊕ A1) ≃ A :=
    (Equiv.Set.union hdisj).symm.trans <| Equiv.setCongr hunion
  calc
    ∑ x : A, f x = ∑ z : ((A0 \ A1 : Set E) ⊕ A1), f (e z) := by
      simpa using (Equiv.sum_comp e (fun x : A ↦ f x)).symm
    _ = (∑ x : ((A0 \ A1 : Set E)), f (e (Sum.inl x))) + ∑ x : A1, f (e (Sum.inr x)) := by
      rw [Fintype.sum_sum_type]
    _ = (∑ x : ((A0 \ A1 : Set E)), f x) + ∑ x : A1, f x := by
      simp [e]

private theorem sum_eq_sum_union_add_sum_compl (A0 A1 : Set E) (f : E → ℝ) :
    let A : Set E := A0 ∪ A1
    (∑ x : E, f x) = (∑ x : A, f x) + ∑ x : ((Aᶜ : Set E)), f x := by
  set A : Set E := A0 ∪ A1
  let e : A ⊕ ((Aᶜ : Set E)) ≃ E := Equiv.Set.sumCompl A
  calc
    ∑ x : E, f x = ∑ z : A ⊕ ((Aᶜ : Set E)), f (e z) := by
      simpa using (Equiv.sum_comp e f).symm
    _ = (∑ x : A, f (e (Sum.inl x))) + ∑ x : ((Aᶜ : Set E)), f (e (Sum.inr x)) := by
      rw [Fintype.sum_sum_type]
    _ = (∑ x : A, f x) + ∑ x : ((Aᶜ : Set E)), f x := by
      simp [e]

private theorem antisymm_energy_sum_eq_two_mul (I : E → E → ℝ) (w : E → ℝ)
    (hantisymm : ∀ x y : E, I x y = -I y x) :
    ∑ x : E, ∑ y : E, (w x - w y) * I x y = 2 * ∑ x : E, w x * netFlowAt I x := by
  calc
    ∑ x : E, ∑ y : E, (w x - w y) * I x y
        = ∑ x : E, ((∑ y : E, w x * I x y) - ∑ y : E, w y * I x y) := by
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            calc
              ∑ y : E, (w x - w y) * I x y = ∑ y : E, (w x * I x y - w y * I x y) := by
                  refine Finset.sum_congr rfl fun y _ ↦ ?_
                  ring
              _ = (∑ y : E, w x * I x y) - ∑ y : E, w y * I x y := by
                  rw [Finset.sum_sub_distrib]
    _ = (∑ x : E, w x * netFlowAt I x) - ∑ x : E, ∑ y : E, w y * I x y := by
          simp [netFlowAt, Finset.mul_sum]
    _ = (∑ x : E, w x * netFlowAt I x) - ∑ y : E, w y * ∑ x : E, I x y := by
          rw [Finset.sum_comm]
          simp [Finset.mul_sum]
    _ = (∑ x : E, w x * netFlowAt I x) - ∑ y : E, w y * (-netFlowAt I y) := by
          refine congrArg (fun t : ℝ ↦ (∑ x : E, w x * netFlowAt I x) - t) ?_
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          congr 1
          calc
            ∑ x : E, I x y = ∑ x : E, -I y x := by
              refine Finset.sum_congr rfl fun x _ ↦ ?_
              rw [hantisymm x y]
            _ = -netFlowAt I y := by simp [netFlowAt]
    _ = 2 * ∑ x : E, w x * netFlowAt I x := by
          simp_rw [mul_neg]
          rw [Finset.sum_neg_distrib]
          ring

-- Proof sketch: expand the double sum into the difference of the two boundary contributions
-- `∑ x, w x * ∑ y, I x y` and `∑ y, w y * ∑ x, I x y`; antisymmetry turns the second term into
-- the negative of the first. Kirchhoff's rule kills the interior contributions on
-- `E \ (A0 ∪ A1)`, and the constancy of `w` on `A0` and `A1` identifies the remaining boundary
-- sums with `w0 * netFlowOnSet I A0` and `w1 * netFlowOnSet I A1`. Finally, use the zero
-- total boundary flux on `A0 ∪ A1` to replace the `A0` contribution by the negative of the `A1`
-- contribution.
/-- Theorem 19.20: conservation of energy. For a flow on `E \ (A0 ∪ A1)`, if the potential `w` is
constant with value `w0` on `A0` and constant with value `w1` on `A1`, then the boundary flux
through `A1` times the potential difference `w1 - w0` equals half of the antisymmetric energy sum
`∑ x, ∑ y, (w x - w y) * I x y`. The textbook notation `I(A1)` is formalized as
`netFlowOnSet I A1`. -/
theorem conservation_of_energy_of_boundary_constant_potential
    {A0 A1 : Set E} {I : E → E → ℝ} {w : E → ℝ} {w0 w1 : ℝ}
    (hI : IsFlowOutside (A0 ∪ A1) I)
    (hw0 : Set.EqOn w (fun _ : E ↦ w0) A0)
    (hw1 : Set.EqOn w (fun _ : E ↦ w1) A1) :
    (w1 - w0) * netFlowOnSet I A1 =
      (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (w x - w y) * I x y := by
  set A : Set E := A0 ∪ A1
  let F0 : ℝ := ∑ x : ((A0 \ A1 : Set E)), netFlowAt I x
  have hA : IsFlowOutside A I := by
    simpa [A] using hI
  have hsplit_boundary0 := sum_union_eq_sum_diff_add_sum A0 A1 (fun x ↦ netFlowAt I x)
  dsimp at hsplit_boundary0
  have hsplit_boundary : (∑ x : A, netFlowAt I x) = F0 + netFlowOnSet I A1 := by
    calc
      ∑ x : A, netFlowAt I x
          = (∑ x : ((A0 \ A1 : Set E)), netFlowAt I x) + ∑ x : A1, netFlowAt I x := hsplit_boundary0
      _ = F0 + netFlowOnSet I A1 := by
            simp [F0, netFlowOnSet_def]
  have htotal_zero : ∑ x : E, netFlowAt I x = 0 := sum_netFlowAt_eq_zero hI.antisymm
  have hboundary_total0 := sum_eq_sum_union_add_sum_compl A0 A1 (fun x ↦ netFlowAt I x)
  dsimp at hboundary_total0
  have hcompl_zero : ∑ x : ((Aᶜ : Set E)), netFlowAt I x = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    exact hA.netFlowAt_eq_zero x.2
  have hboundary_zero : ∑ x : A, netFlowAt I x = 0 := by
    rw [hboundary_total0, hcompl_zero, add_zero] at htotal_zero
    exact htotal_zero
  have hflux_sum : F0 + netFlowOnSet I A1 = 0 := by
    simpa [hsplit_boundary] using hboundary_zero
  have hflux_diff : F0 = -netFlowOnSet I A1 := by
    linarith
  have hweighted_boundary0 := sum_union_eq_sum_diff_add_sum A0 A1 (fun x ↦ w x * netFlowAt I x)
  dsimp at hweighted_boundary0
  have hweighted_boundary :
      ∑ x : A, w x * netFlowAt I x = w0 * F0 + w1 * netFlowOnSet I A1 := by
    calc
      ∑ x : A, w x * netFlowAt I x
          = (∑ x : ((A0 \ A1 : Set E)), w x * netFlowAt I x) + ∑ x : A1, w x * netFlowAt I x :=
              hweighted_boundary0
      _ = w0 * F0 + ∑ x : A1, w x * netFlowAt I x := by
            congr 1
            calc
              ∑ x : ((A0 \ A1 : Set E)), w x * netFlowAt I x
                  = ∑ x : ((A0 \ A1 : Set E)), w0 * netFlowAt I x := by
                      refine Finset.sum_congr rfl fun x _ ↦ ?_
                      have hxw : w x = w0 := by
                        simpa using hw0 x.2.1
                      rw [hxw]
              _ = w0 * F0 := by
                    simp [F0, Finset.mul_sum]
      _ = w0 * F0 + w1 * netFlowOnSet I A1 := by
            congr 1
            calc
              ∑ x : A1, w x * netFlowAt I x = ∑ x : A1, w1 * netFlowAt I x := by
                  refine Finset.sum_congr rfl fun x _ ↦ ?_
                  have hxw : w x = w1 := by
                    simpa using hw1 x.2
                  rw [hxw]
              _ = w1 * netFlowOnSet I A1 := by
                    rw [netFlowOnSet_def, ← Finset.mul_sum]
  have hweighted_total0 := sum_eq_sum_union_add_sum_compl A0 A1 (fun x ↦ w x * netFlowAt I x)
  dsimp at hweighted_total0
  have hweighted_total : ∑ x : E, w x * netFlowAt I x = ∑ x : A, w x * netFlowAt I x := by
    have hcompl : ∑ x : ((Aᶜ : Set E)), w x * netFlowAt I x = 0 := by
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      have hx0 : netFlowAt I x = 0 := hA.netFlowAt_eq_zero x.2
      simp [hx0]
    rw [hweighted_total0, hcompl, add_zero]
  have hweighted : ∑ x : E, w x * netFlowAt I x = (w1 - w0) * netFlowOnSet I A1 := by
    calc
      ∑ x : E, w x * netFlowAt I x = w0 * F0 + w1 * netFlowOnSet I A1 := by
        rw [hweighted_total, hweighted_boundary]
      _ = w0 * (-netFlowOnSet I A1) + w1 * netFlowOnSet I A1 := by
            rw [hflux_diff]
      _ = (w1 - w0) * netFlowOnSet I A1 := by
            ring
  have henergy :
      ∑ x : E, ∑ y : E, (w x - w y) * I x y = 2 * ((w1 - w0) * netFlowOnSet I A1) := by
    rw [antisymm_energy_sum_eq_two_mul I w hI.antisymm, hweighted]
  have hhalf :
      (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (w x - w y) * I x y = (w1 - w0) * netFlowOnSet I A1 := by
    rw [henergy]
    ring
  exact hhalf.symm

end ProbabilityTheory
