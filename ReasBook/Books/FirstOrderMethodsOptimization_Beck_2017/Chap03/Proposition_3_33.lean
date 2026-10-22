/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_32
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

noncomputable section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

recall IsMinOn
recall fermatWeberObjective
recall euclidean_subdifferentialAt_fermatWeberObjective_eq_singleton_of_not_mem_range
recall euclidean_subdifferentialAt_fermatWeberObjective_eq_image_closedBall_at_site

/- This file records a `source-facing` optimality criterion for the owner objective
`fermatWeberObjective`. The Euclidean subdifferential formulas already belong to Proposition 3.32,
so this file reuses those canonical companions and adds only the textbook balance and residual
optimality criteria. -/

/-- The weighted normalized displacement vector from the site `a i` to `x` appearing in the
Fermat--Weber balance condition. -/
def fermatWeberBalanceTerm (ω : Fin m → ℝ) (a : Fin m → E) (x : E) (i : Fin m) : E :=
  ω i • ((‖x - a i‖)⁻¹ • (x - a i))

/-- The residual balance vector at the site `a j`, obtained by summing the weighted normalized
displacement vectors from the remaining sites to `a j`. -/
def fermatWeberResidualBalance (ω : Fin m → ℝ) (a : Fin m → E) (j : Fin m) : E :=
  (Finset.univ.erase j).sum (fermatWeberBalanceTerm ω a (a j))

@[simp] theorem fermatWeberBalanceTerm_apply
    (ω : Fin m → ℝ) (a : Fin m → E) (x : E) (i : Fin m) :
    fermatWeberBalanceTerm ω a x i = ω i • ((‖x - a i‖)⁻¹ • (x - a i)) := rfl

@[simp] theorem fermatWeberResidualBalance_eq_sum_erase
    (ω : Fin m → ℝ) (a : Fin m → E) (j : Fin m) :
    fermatWeberResidualBalance ω a j =
      (Finset.univ.erase j).sum (fermatWeberBalanceTerm ω a (a j)) := rfl

/-- Helper for Proposition 3.33: the zero vector lies in the translate of
`closedBall (0 : E) r` by `s` exactly when `‖s‖ ≤ r`. -/
private lemma zero_mem_translateClosedBall_iff_norm_le
    (s : E) (r : ℝ) :
    (0 : E) ∈ (fun v : E ↦ s + v) '' Metric.closedBall (0 : E) r ↔ ‖s‖ ≤ r := by
  constructor
  · rintro ⟨v, hv, hv0⟩
    have hv_eq : v = -s := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using hv0
    have hv_norm : ‖v‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    simpa [hv_eq, norm_neg] using hv_norm
  · intro hs
    refine ⟨-s, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm, norm_neg] using hs
    · simp

/-- Helper for Proposition 3.33: under nonnegative weights, a point `x` outside
`Set.range a` globally minimizes the Fermat--Weber objective if and only if the weighted
normalized displacement vectors balance to zero. -/
theorem isMinOn_fermatWeberObjective_iff_balance_of_not_mem_range
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E)
    (x : E) (hx : x ∉ Set.range a) :
    IsMinOn (fermatWeberObjective ω a) Set.univ x ↔
      ∑ i, fermatWeberBalanceTerm ω a x i = 0 := by
  rw [isMinOn_univ_iff_zero_mem_subdifferentialAt]
  have hzero :
      ((0 : StrongDual ℝ E) ∈ subdifferentialAt (fermatWeberObjective ω a) x) ↔
        (0 : E) ∈ euclideanSubdifferentialAt (fermatWeberObjective ω a) x := by
    rw [← (InnerProductSpace.toDualMap ℝ E).map_zero]
    exact (mem_euclideanSubdifferentialAt_iff).symm
  rw [hzero,
    euclidean_subdifferentialAt_fermatWeberObjective_eq_singleton_of_not_mem_range ω hω a x hx]
  simp [Set.mem_singleton_iff, fermatWeberBalanceTerm, eq_comm]

/-- Helper for Proposition 3.33: under nonnegative weights and pairwise distinct sites,
`a j` globally minimizes the Fermat--Weber objective if and only if the residual balance over the
remaining sites has norm at most `ω j`. -/
theorem isMinOn_fermatWeberObjective_iff_residualBound_at_site
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E) (ha : Function.Injective a)
    (j : Fin m) :
    IsMinOn (fermatWeberObjective ω a) Set.univ (a j) ↔
      ‖fermatWeberResidualBalance ω a j‖ ≤ ω j := by
  rw [isMinOn_univ_iff_zero_mem_subdifferentialAt]
  have hzero :
      ((0 : StrongDual ℝ E) ∈ subdifferentialAt (fermatWeberObjective ω a) (a j)) ↔
        (0 : E) ∈ euclideanSubdifferentialAt (fermatWeberObjective ω a) (a j) := by
    rw [← (InnerProductSpace.toDualMap ℝ E).map_zero]
    exact (mem_euclideanSubdifferentialAt_iff).symm
  rw [hzero,
    euclidean_subdifferentialAt_fermatWeberObjective_eq_image_closedBall_at_site ω hω a ha j]
  rw [zero_mem_translateClosedBall_iff_norm_le]
  simp [fermatWeberResidualBalance, fermatWeberBalanceTerm]

-- Proof sketch: apply the real-valued Fermat criterion
-- `isMinOn_univ_iff_zero_mem_subdifferentialAt`, then split according to whether `x` is one of
-- the sites. The off-site branch is exactly the balance criterion above, and the on-site branch
-- is exactly the residual translated-ball criterion above.
/-- Proposition 3.33: for pairwise distinct sites and nonnegative weights, a point globally
minimizes the Fermat--Weber objective if and only if either it is not one of the sites and the
weighted normalized displacement vectors sum to zero, or it equals a site `a_j` and the norm of
the corresponding residual sum over the remaining sites is at most `ω_j`. -/
theorem isMinOn_fermatWeberObjective_iff_balance_or_site_bound
    (ω : Fin m → ℝ) (a : Fin m → E) (ha : Function.Injective a)
    (hω : ∀ i, 0 ≤ ω i) (x : E) :
    IsMinOn (fermatWeberObjective ω a) Set.univ x ↔
      (x ∉ Set.range a ∧ ∑ i, fermatWeberBalanceTerm ω a x i = 0) ∨
        ∃ j : Fin m, x = a j ∧ ‖fermatWeberResidualBalance ω a j‖ ≤ ω j := by
  classical
  by_cases hx : x ∈ Set.range a
  · rcases hx with ⟨j, rfl⟩
    rw [isMinOn_fermatWeberObjective_iff_residualBound_at_site ω hω a ha j]
    constructor
    · intro hmin
      exact Or.inr ⟨j, rfl, hmin⟩
    · rintro (hOff | hOn)
      · exact False.elim (hOff.1 ⟨j, rfl⟩)
      · rcases hOn with ⟨k, hkx, hkbound⟩
        have hk : k = j := by
          apply ha
          simpa using hkx.symm
        subst hk
        simpa using hkbound
  · rw [isMinOn_fermatWeberObjective_iff_balance_of_not_mem_range ω hω a x hx]
    constructor
    · intro hbalance
      exact Or.inl ⟨hx, hbalance⟩
    · rintro (hOff | hOn)
      · exact hOff.2
      · rcases hOn with ⟨j, hxj, _⟩
        exact False.elim (hx ⟨j, hxj.symm⟩)

end
