/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_15

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

/- Domain-style sampling for Theorem 19.19:
- `source-facing`: the finite-boundary effective conductance `C_eff(A0 ↔ A1)`.
- `core/canonical`: `electricalCurrent`, `IsElectricalPotential`, `netFlowOnSet`, and the
  Chapter 19 quadratic-energy pattern already used for electrical flows.
- `bridge/view`: Definition 19.17 identifies `C_eff(A0 ↔ A1)` with the boundary current of a
  unit-voltage electrical potential, so the current-based formula belongs as companion API rather
  than as the owner statement. -/

attribute [local instance] Classical.propDecidable

variable {E : Type u} [Fintype E]
variable {C C' : E → E → ℝ≥0∞}
variable {A0 A1 : Set E} {u u' : E → ℝ}

/-- The Dirichlet energy of a potential `u` on the conductance network `C`. -/
def dirichletEnergy (C : E → E → ℝ≥0∞) (u : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (C x y).toReal * (u x - u y) ^ (2 : ℕ)

/-- The finite-boundary effective conductance between `A0` and `A1`, defined intrinsically as the
infimum of the Dirichlet energies of unit-boundary potentials. -/
def effectiveConductance (C : E → E → ℝ≥0∞) (A0 A1 : Set E) : ℝ :=
  sInf <|
    dirichletEnergy C ''
      {u : E → ℝ | Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}

/-- Helper for Theorem 19.19: split a finite sum over `A0 ∪ A1` into the disjoint pieces
`A0 \ A1` and `A1`. -/
private theorem sum_union_eq_sum_diff_add_sum (A0 A1 : Set E) (f : E → ℝ) :
    let A : Set E := A0 ∪ A1
    (∑ x : A, f x) = (∑ x : ((A0 \ A1 : Set E)), f x) + ∑ x : A1, f x := by
  -- Reindex the union along the canonical equivalence with the corresponding sum type.
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

/-- Helper for Theorem 19.19: split a finite sum over all vertices into the boundary part
`A0 ∪ A1` and its complement. -/
private theorem sum_eq_sum_union_add_sum_compl (A0 A1 : Set E) (f : E → ℝ) :
    let A : Set E := A0 ∪ A1
    (∑ x : E, f x) = (∑ x : A, f x) + ∑ x : ((Aᶜ : Set E)), f x := by
  -- Reindex the whole space as the disjoint union of the boundary and its complement.
  set A : Set E := A0 ∪ A1
  let e : A ⊕ ((Aᶜ : Set E)) ≃ E := Equiv.Set.sumCompl A
  calc
    ∑ x : E, f x = ∑ z : A ⊕ ((Aᶜ : Set E)), f (e z) := by
      simpa using (Equiv.sum_comp e f).symm
    _ = (∑ x : A, f (e (Sum.inl x))) + ∑ x : ((Aᶜ : Set E)), f (e (Sum.inr x)) := by
          rw [Fintype.sum_sum_type]
    _ = (∑ x : A, f x) + ∑ x : ((Aᶜ : Set E)), f x := by
          simp [e]

/-- Helper for Theorem 19.19: rewrite the antisymmetric edge-energy sum as twice the weighted
vertex flux sum. -/
private theorem antisymm_energy_sum_eq_two_mul (I : E → E → ℝ) (w : E → ℝ)
    (hantisymm : ∀ x y : E, I x y = -I y x) :
    ∑ x : E, ∑ y : E, (w x - w y) * I x y = 2 * ∑ x : E, w x * netFlowAt I x := by
  -- Expand the edge difference term and then use antisymmetry to identify the second half.
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
            _ = -netFlowAt I y := by
                  simp [netFlowAt]
    _ = 2 * ∑ x : E, w x * netFlowAt I x := by
          simp_rw [mul_neg]
          rw [Finset.sum_neg_distrib]
          ring

/-- Helper for Theorem 19.19: if a flow is supported outside `A0 ∪ A1` and the test potential is
constant on both boundary parts, then the boundary current equals the corresponding energy sum. -/
private theorem boundaryConstantPotential_energyIdentity
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
  -- First rewrite the total boundary flux as the contribution from `A0 \ A1` and `A1`.
  have hsplit_boundary0 := sum_union_eq_sum_diff_add_sum A0 A1 (fun x ↦ netFlowAt I x)
  dsimp at hsplit_boundary0
  have hsplit_boundary : (∑ x : A, netFlowAt I x) = F0 + netFlowOnSet I A1 := by
    calc
      ∑ x : A, netFlowAt I x
          = (∑ x : ((A0 \ A1 : Set E)), netFlowAt I x) + ∑ x : A1, netFlowAt I x :=
            hsplit_boundary0
      _ = F0 + netFlowOnSet I A1 := by
            simp [F0, netFlowOnSet_def]
  -- Kirchhoff's rule off the boundary forces the total boundary flux to vanish.
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
  -- The weighted boundary sum collapses because `w` is constant on both boundary pieces.
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
  -- Interior contributions vanish, so the weighted total sum is a pure boundary term.
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
  -- The antisymmetric double sum matches twice the weighted flux sum, so we can solve for it.
  have henergy :
      ∑ x : E, ∑ y : E, (w x - w y) * I x y = 2 * ((w1 - w0) * netFlowOnSet I A1) := by
    rw [antisymm_energy_sum_eq_two_mul I w hI.antisymm, hweighted]
  have hhalf :
      (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (w x - w y) * I x y = (w1 - w0) * netFlowOnSet I A1 := by
    rw [henergy]
    ring
  exact hhalf.symm

/-- Helper for Theorem 19.19: for a unit-voltage electrical potential, the boundary current equals
its Dirichlet energy. -/
private theorem netFlowOnSet_electricalCurrent_eq_dirichletEnergy
    (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1) :
    netFlowOnSet (electricalCurrent C u) A1 = dirichletEnergy C u := by
  -- Route correction: identify the boundary current via the local conservation law, not via later
  -- Thomson-principle infrastructure.
  have hidentity :=
    boundaryConstantPotential_energyIdentity hu hu0 hu1
  calc
    netFlowOnSet (electricalCurrent C u) A1
        = (1 - 0) * netFlowOnSet (electricalCurrent C u) A1 := by
            ring
    _ = (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (u x - u y) * electricalCurrent C u x y := by
          simpa using hidentity
    _ = dirichletEnergy C u := by
          -- Unfold the induced current once so the edge contribution is the square term.
          unfold dirichletEnergy
          refine congrArg ((1 / 2 : ℝ) * ·) ?_
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [electricalCurrent_apply]
          ring

/-- Helper for Theorem 19.19: expanding the energy of `u + w` separates the base, mixed, and error
terms. -/
private theorem dirichletEnergy_add_decomposition
    (C : E → E → ℝ≥0∞) (u w : E → ℝ) :
    dirichletEnergy C (fun x ↦ u x + w x) =
      dirichletEnergy C u +
        ∑ x : E, ∑ y : E, (w x - w y) * electricalCurrent C u x y +
        dirichletEnergy C w := by
  -- Move the factor `1 / 2` inside the sums, prove the edgewise identity, then regroup the sums.
  calc
    dirichletEnergy C (fun x ↦ u x + w x)
        = ∑ x : E, ∑ y : E,
            (1 / 2 : ℝ) * ((C x y).toReal * ((u x + w x) - (u y + w y)) ^ (2 : ℕ)) := by
              unfold dirichletEnergy
              simp_rw [Finset.mul_sum]
    _ = ∑ x : E, ∑ y : E,
          ((1 / 2 : ℝ) * ((C x y).toReal * (u x - u y) ^ (2 : ℕ)) +
            (w x - w y) * electricalCurrent C u x y +
            (1 / 2 : ℝ) * ((C x y).toReal * (w x - w y) ^ (2 : ℕ))) := by
              refine Finset.sum_congr rfl fun x _ ↦ ?_
              refine Finset.sum_congr rfl fun y _ ↦ ?_
              rw [electricalCurrent_apply]
              ring
    _ = (∑ x : E, ∑ y : E, (1 / 2 : ℝ) * ((C x y).toReal * (u x - u y) ^ (2 : ℕ))) +
          ∑ x : E, ∑ y : E, (w x - w y) * electricalCurrent C u x y +
          ∑ x : E, ∑ y : E, (1 / 2 : ℝ) * ((C x y).toReal * (w x - w y) ^ (2 : ℕ)) := by
            simp_rw [Finset.sum_add_distrib]
    _ = dirichletEnergy C u +
          ∑ x : E, ∑ y : E, (w x - w y) * electricalCurrent C u x y +
          dirichletEnergy C w := by
            unfold dirichletEnergy
            simp_rw [Finset.mul_sum]

/-- Helper for Theorem 19.19: every Dirichlet energy is nonnegative because it is a weighted sum of
squares with nonnegative coefficients. -/
private theorem dirichletEnergy_nonneg (C : E → E → ℝ≥0∞) (u : E → ℝ) :
    0 ≤ dirichletEnergy C u := by
  -- Each edge contributes a nonnegative coefficient times a square.
  unfold dirichletEnergy
  refine mul_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg fun x _ ↦ ?_
  refine Finset.sum_nonneg fun y _ ↦ ?_
  exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

/-- Helper for Theorem 19.19: an electrical potential minimizes the Dirichlet energy among all
potentials with the same boundary values. -/
private theorem dirichletEnergy_le_of_electricalPotential
    {v : E → ℝ} (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1)
    (hv0 : Set.EqOn v (fun _ : E ↦ 0) A0)
    (hv1 : Set.EqOn v (fun _ : E ↦ 1) A1) :
    dirichletEnergy C u ≤ dirichletEnergy C v := by
  let w : E → ℝ := fun x ↦ v x - u x
  have hw0 : Set.EqOn w (fun _ : E ↦ 0) A0 := by
    intro x hx
    simp [w, hu0 hx, hv0 hx]
  have hw1 : Set.EqOn w (fun _ : E ↦ 0) A1 := by
    intro x hx
    simp [w, hu1 hx, hv1 hx]
  have hcross_half :=
    boundaryConstantPotential_energyIdentity hu hw0 hw1
  have hcross :
      ∑ x : E, ∑ y : E, (w x - w y) * electricalCurrent C u x y = 0 := by
    have hhalf :
        (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (w x - w y) * electricalCurrent C u x y = 0 := by
      simpa using hcross_half.symm
    linarith
  have hw_nonneg : 0 ≤ dirichletEnergy C w := dirichletEnergy_nonneg C w
  have hv_eq : v = fun x ↦ u x + w x := by
    funext x
    simp [w]
  -- Expand `v = u + w`, kill the mixed term by conservation of energy, and keep the nonnegative
  -- remainder.
  rw [hv_eq, dirichletEnergy_add_decomposition]
  rw [hcross]
  linarith

/-- Helper for Theorem 19.19: decreasing conductances decreases the Dirichlet energy of every
potential. -/
private theorem dirichletEnergy_mono_of_conductance_le
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC'_finite : ∀ x : E, conductance C' x < ∞)
    (hCC' : ∀ x y : E, C' x y ≤ C x y) (u : E → ℝ) :
    dirichletEnergy C' u ≤ dirichletEnergy C u := by
  -- Route correction: row finiteness keeps every edge conductance finite, so `ENNReal.toReal`
  -- preserves the pointwise order before we compare the weighted square sums.
  have hC_edge_finite : ∀ x y : E, C x y ≠ ∞ := by
    intro x y
    have hxy_le : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : E, C x z)
    exact ne_of_lt (lt_of_le_of_lt hxy_le (hC_finite x))
  have hC'_edge_finite : ∀ x y : E, C' x y ≠ ∞ := by
    intro x y
    have hxy_le : C' x y ≤ conductance C' x := by
      simpa [conductance] using (ENNReal.le_tsum y : C' x y ≤ ∑' z : E, C' x z)
    exact ne_of_lt (lt_of_le_of_lt hxy_le (hC'_finite x))
  unfold dirichletEnergy
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (1 / 2 : ℝ))
  refine Finset.sum_le_sum fun x _ ↦ ?_
  refine Finset.sum_le_sum fun y _ ↦ ?_
  have hcoeff : (C' x y).toReal ≤ (C x y).toReal :=
    ENNReal.toReal_mono (hC_edge_finite x y) (hCC' x y)
  have hsquare_nonneg : 0 ≤ (u x - u y) ^ (2 : ℕ) := sq_nonneg (u x - u y)
  exact mul_le_mul_of_nonneg_right hcoeff hsquare_nonneg

-- Proof sketch: Definition 19.17 identifies the effective conductance with the boundary current
-- of the electrical current induced by any unit-voltage electrical potential between `A0` and
-- `A1`; this realizes the infimum in `effectiveConductance`.
/-- For a unit-voltage electrical potential between disjoint nonempty boundary sets, the owner
`effectiveConductance C A0 A1` is the boundary current through `A1`. -/
theorem effectiveConductance_eq_netFlowOnSet_electricalCurrent
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1) :
    effectiveConductance C A0 A1 =
      netFlowOnSet (electricalCurrent C u) A1 := by
  -- Rewrite the target current as the energy of the chosen electrical potential.
  have hflow_eq_energy :
      netFlowOnSet (electricalCurrent C u) A1 = dirichletEnergy C u :=
    netFlowOnSet_electricalCurrent_eq_dirichletEnergy hu hu0 hu1
  have hchosen :
      dirichletEnergy C u ∈
        dirichletEnergy C ''
          {v : E → ℝ | Set.EqOn v (fun _ : E ↦ 0) A0 ∧ Set.EqOn v (fun _ : E ↦ 1) A1} := by
    exact ⟨u, ⟨hu0, hu1⟩, rfl⟩
  let S : Set ℝ :=
    dirichletEnergy C ''
      {v : E → ℝ | Set.EqOn v (fun _ : E ↦ 0) A0 ∧ Set.EqOn v (fun _ : E ↦ 1) A1}
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact dirichletEnergy_nonneg C v
  have hS_nonempty : S.Nonempty := ⟨dirichletEnergy C u, by simpa [S] using hchosen⟩
  unfold effectiveConductance
  change sInf S = netFlowOnSet (electricalCurrent C u) A1
  refine le_antisymm ?_ ?_
  · -- The chosen electrical potential is one admissible competitor in the infimum.
    calc
      sInf S
          ≤ dirichletEnergy C u := by
              exact csInf_le hS_bddBelow (by simpa [S] using hchosen)
      _ = netFlowOnSet (electricalCurrent C u) A1 := hflow_eq_energy.symm
  · -- Every other admissible potential has at least the same energy as the electrical one.
    calc
      netFlowOnSet (electricalCurrent C u) A1 = dirichletEnergy C u := hflow_eq_energy
      _ ≤ sInf S := by
            refine le_csInf hS_nonempty ?_
            intro r hr
            rcases hr with ⟨v, ⟨hv0, hv1⟩, rfl⟩
            exact dirichletEnergy_le_of_electricalPotential hu hu0 hu1 hv0 hv1

-- Proof sketch: the Dirichlet-energy infimum defining `effectiveConductance` is monotone in the
-- conductance family because every admissible unit-boundary potential has smaller energy for `C'`
-- than for `C` when `C' ≤ C` pointwise. The nonempty and disjoint boundary hypotheses are the
-- textbook assumptions for the finite-boundary conductance problem.
/-- Theorem 19.19: Rayleigh's monotonicity principle. For symmetric conductance families `C` and
`C'` with finite total conductance at every vertex, if `C' x y ≤ C x y` for all `x, y`, then the
effective conductance `C_eff(A0 ↔ A1)` of the network with conductances `C` is at least the
effective conductance for `C'`. -/
theorem rayleigh_monotonicity_principle
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC'_symm : ∀ x y : E, C' x y = C' y x)
    (hC'_finite : ∀ x : E, conductance C' x < ∞)
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hCC' : ∀ x y : E, C' x y ≤ C x y) :
    effectiveConductance C A0 A1 ≥ effectiveConductance C' A0 A1 := by
  -- Route correction: compare the two conductance problems on the same admissible potentials
  -- instead of unfolding later electrical-current infrastructure.
  let admissible : Set (E → ℝ) :=
    {v : E → ℝ | Set.EqOn v (fun _ : E ↦ 0) A0 ∧ Set.EqOn v (fun _ : E ↦ 1) A1}
  let S : Set ℝ := dirichletEnergy C '' admissible
  let S' : Set ℝ := dirichletEnergy C' '' admissible
  let boundaryPotential : E → ℝ := fun x ↦ if x ∈ A1 then 1 else 0
  have hdisj_left : ∀ ⦃x : E⦄, x ∈ A0 → x ∈ A1 → False := Set.disjoint_left.mp hdisj
  have hboundary0 : Set.EqOn boundaryPotential (fun _ : E ↦ 0) A0 := by
    -- On `A0`, disjointness rules out the `A1` branch of the witness potential.
    intro x hx
    have hxA1 : x ∉ A1 := fun hx1 ↦ hdisj_left hx hx1
    simp [boundaryPotential, hxA1]
  have hboundary1 : Set.EqOn boundaryPotential (fun _ : E ↦ 1) A1 := by
    -- On `A1`, the witness potential is constantly equal to `1`.
    intro x hx
    simp [boundaryPotential, hx]
  have hS_nonempty : S.Nonempty := by
    refine ⟨dirichletEnergy C boundaryPotential, ?_⟩
    exact ⟨boundaryPotential, ⟨hboundary0, hboundary1⟩, rfl⟩
  have hS'_bddBelow : BddBelow S' := by
    -- Every Dirichlet energy in the `C'`-network is nonnegative.
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨v, hv, rfl⟩
    exact dirichletEnergy_nonneg C' v
  unfold effectiveConductance
  change sInf S' ≤ sInf S
  refine le_csInf hS_nonempty ?_
  intro r hr
  rcases hr with ⟨v, ⟨hv0, hv1⟩, rfl⟩
  have hmemS' : dirichletEnergy C' v ∈ S' := ⟨v, ⟨hv0, hv1⟩, rfl⟩
  -- The same admissible potential belongs to both infimum sets, so pointwise energy monotonicity
  -- transfers directly to the infima.
  exact le_trans (csInf_le hS'_bddBelow hmemS')
    (dirichletEnergy_mono_of_conductance_le hC_finite hC'_finite hCC' v)

-- Proof sketch: rewrite both effective conductances via
-- `effectiveConductance_eq_netFlowOnSet_electricalCurrent`, then apply the owner-level Rayleigh
-- monotonicity theorem.
/-- For unit-voltage electrical potentials on the two conductance networks, Rayleigh monotonicity
rewrites as the corresponding boundary-current inequality. -/
theorem rayleigh_monotonicity_principle_netFlowOnSet
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC'_symm : ∀ x y : E, C' x y = C' y x)
    (hC'_finite : ∀ x : E, conductance C' x < ∞)
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hCC' : ∀ x y : E, C' x y ≤ C x y)
    (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1)
    (hu' : IsElectricalPotential C' (A0 ∪ A1) u')
    (hu'0 : Set.EqOn u' (fun _ : E ↦ 0) A0)
    (hu'1 : Set.EqOn u' (fun _ : E ↦ 1) A1) :
    netFlowOnSet (electricalCurrent C u) A1 ≥
      netFlowOnSet (electricalCurrent C' u') A1 := by
  -- Rewrite both boundary currents through effective conductance, then insert the owner theorem.
  calc
    netFlowOnSet (electricalCurrent C u) A1 = effectiveConductance C A0 A1 := by
      symm
      exact effectiveConductance_eq_netFlowOnSet_electricalCurrent hA0 hA1 hdisj hu hu0 hu1
    _ ≥ effectiveConductance C' A0 A1 := by
      exact rayleigh_monotonicity_principle
        hC_symm hC_finite hC'_symm hC'_finite hA0 hA1 hdisj hCC'
    _ = netFlowOnSet (electricalCurrent C' u') A1 := by
      exact effectiveConductance_eq_netFlowOnSet_electricalCurrent hA0 hA1 hdisj hu' hu'0 hu'1

end ProbabilityTheory
