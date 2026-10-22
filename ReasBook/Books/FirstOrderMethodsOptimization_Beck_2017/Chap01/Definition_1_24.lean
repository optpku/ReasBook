/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {ι : Type*}

/- Definition 1.24 is `source-facing`: it introduces the coordinate box owner `Box[ℓ,u]` with
extended-real endpoints. The textbook box in `ℝ^n` with finite real bounds is the specialization
of this owner obtained by coercing the endpoints to `EReal`, and that specialization agrees with
the pointwise interval `Set.Icc`. -/

/-- The coordinate box in `ι → ℝ` with extended-real lower and upper bounds. -/
def box (ℓ u : ι → EReal) : Set (ι → ℝ) :=
  {x | ∀ i, ℓ i ≤ (x i : EReal) ∧ (x i : EReal) ≤ u i}

notation "Box[" ℓ "," u "]" => box ℓ u

-- Proof sketch: unfold `Box[ℓ,u]`; membership is definitionally the coordinatewise bound
-- condition.
/-- A point lies in `Box[ℓ,u]` exactly when each coordinate lies between the corresponding
extended-real lower and upper bounds. -/
@[simp] theorem mem_box_iff {ℓ u : ι → EReal} {x : ι → ℝ} :
    x ∈ Box[ℓ,u] ↔ ∀ i, ℓ i ≤ (x i : EReal) ∧ (x i : EReal) ≤ u i :=
  Iff.rfl

-- Proof sketch: `Box[ℓ,u]` is the product of the closed coordinate intervals
-- `((↑) : ℝ → EReal) ⁻¹' Set.Icc (ℓ i) (u i)`, so closedness follows from
-- `isClosed_Icc`, continuity of the coercion `ℝ → EReal`, and `isClosed_set_pi`.
/-- The coordinate box `Box[ℓ,u]` is closed in the product coordinate space `ι → ℝ`. -/
theorem isClosed_box (ℓ u : ι → EReal) : IsClosed (Box[ℓ,u] : Set (ι → ℝ)) := by
  let s : ι → Set ℝ := fun i ↦ ((fun x : ℝ ↦ (x : EReal)) ⁻¹' Set.Icc (ℓ i) (u i))
  have hs : ∀ i, IsClosed (s i) := by
    intro i
    exact (isClosed_Icc : IsClosed (Set.Icc (ℓ i) (u i))).preimage continuous_coe_real_ereal
  have hbox : (Box[ℓ,u] : Set (ι → ℝ)) = Set.pi Set.univ s := by
    ext x
    simp [s, mem_box_iff]
  rw [hbox]
  exact isClosed_set_pi fun i _ ↦ hs i

/- The textbook box with real endpoints is the finite-endpoint specialization of `Box[ℓ,u]`. -/
#check (Set.Icc : (ι → ℝ) → (ι → ℝ) → Set (ι → ℝ))

-- Proof sketch: both sides express the same pointwise inequalities on `ι → ℝ`; rewrite
-- `Set.Icc` using the product order and simplify the endpoint coercions to `EReal`.
/-- With real endpoints, `Box[ℓ,u]` agrees with the pointwise interval `Set.Icc ℓ u`. -/
theorem box_eq_Icc (ℓ u : ι → ℝ) :
    Box[(fun i ↦ (ℓ i : EReal)), fun i ↦ (u i : EReal)] = Set.Icc ℓ u := by
  ext x
  simp [Set.mem_Icc, Pi.le_def, forall_and]

end
