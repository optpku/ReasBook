/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.29 lies in the chapter's constrained convex minimization / common-certificate domain.

Mandatory domain-style sampling before drafting:
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for constrained minimizers;
- `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing` in `Theorem_3_1_24`, the exact
  earlier optimality criterion reused here;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the pointwise normal-cone owner;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the owner for common subdifferentials.

Best owner abstraction:
- the constrained minimizer set `argmin[Q] f`;
- the pointwise normal cone `N[Q] x`;
- the common regular subdifferential `∂̂ f(X)`.

Primitive data:
- a feasible set `Q`;
- a real-valued objective `f`;
- an optimal point `xStar`;
- a subgradient certificate `gStar`.

Derived API introduced here:
- the normal-cone owner bridge `NormalCone.common X` and its membership / pairing expansions;
- the propagated common-certificate theorem in source-facing pairing form;
- the owner-level common-normal-cone corollary.

Source/core/bridge triage:
- source-facing: Theorem 3.29's optimality criterion together with the propagated certificate on
  the whole optimal set;
- core/canonical: `argmin[Q] f`, `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing`,
  `normalCone`, and `commonRegularSubdifferential`;
- bridge/view: the common-normal-cone owner `NormalCone.common`, defined as the intersection of
  the pointwise normal cones and paired with its inequality-form expansion.
-/

section OptimalityCriterionRecall

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Helper for Theorem 3.29 [Chapter3_2.json:34]: recall the earlier constrained-optimality
criterion stating that a feasible point `xStar ∈ Q` belongs to `argmin[Q] f` if and only if there
exists a subgradient `gStar ∈ ∂f(xStar)` with nonnegative pairing against every feasible
displacement. The propagated common-subdifferential / common-normal-cone consequence is stated in
the companion theorem below. -/
recall mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)

end OptimalityCriterionRecall

section CommonNormalConeOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

namespace NormalCone

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the common normal cone of `X` is the
intersection of the pointwise normal cones `N[X] x` over all `x ∈ X`. -/
def common (X : Set V) : Set V :=
  ⋂ x ∈ X, N[X] x

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: membership in the common normal cone means
belonging to the normal cone of `X` at every point of `X`. -/
-- Proof sketch: unfold `NormalCone.common`; membership in the iterated intersection is exactly the
-- universal pointwise normal-cone condition.
@[simp] theorem mem_common_iff
    {X : Set V} {g : V} :
    g ∈ common X ↔ ∀ x ∈ X, g ∈ N[X] x := by
  simp [common]

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the common normal-cone owner can be read
entirely through the textbook pairing inequalities at every pair of points of `X`. -/
theorem mem_common_iff_nonneg_pairing
    {X : Set V} {g : V} :
    g ∈ common X ↔ ∀ x ∈ X, ∀ y ∈ X, 0 ≤ inner ℝ g (y - x) := by
  rw [mem_common_iff]
  constructor
  · intro hg x hx y hy
    exact (mem_normalCone_iff.mp (hg x hx)) y hy
  · intro hg x hx
    rw [mem_normalCone_iff]
    intro y hy
    exact hg x hx y hy

end NormalCone

end CommonNormalConeOwner

section CommonCertificatePairing

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: all constrained minimizers have the same
objective value. -/
theorem value_eq_of_mem_argmin
    {Q : Set V} {f : V → ℝ} {xStar x : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hx : x ∈ argmin[Q] f) :
    f x = f xStar := by
  -- Compare the two minimizers against each other using the owner expansion of `argmin`.
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem_Q, hxStar_min⟩
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem_Q, hx_min⟩
  exact le_antisymm (hx_min hxStar_mem_Q) (hxStar_min hx_mem_Q)

end

section DisplacementAlgebra

variable {V : Type u} [NormedAddCommGroup V]

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: split the displacement from `xStar` to `y`
through an intermediate point `x`. -/
private theorem displacement_split
    (y x xStar : V) :
    y - xStar = (y - x) + (x - xStar) := by
  abel

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the displacement from `x` to `y` is the
difference of their displacements from `xStar`. -/
private theorem displacement_difference
    (y x xStar : V) :
    y - x = (y - xStar) - (x - xStar) := by
  abel

end DisplacementAlgebra

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the certificate pairing is tight at every
constrained minimizer. -/
theorem pairing_eq_zero_of_mem_argmin
    {Q : Set V} {f : V → ℝ} {xStar gStar x : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ y ∈ Q, 0 ≤ inner ℝ gStar (y - xStar))
    (hx : x ∈ argmin[Q] f) :
    inner ℝ gStar (x - xStar) = 0 := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem_Q, hx_min⟩
  have hvalue : f x = f xStar := value_eq_of_mem_argmin hxStar hx
  have hsubgrad := mem_subdifferential_coe_real_iff.mp hgStar_sub
  have hnonneg : 0 ≤ inner ℝ gStar (x - xStar) := hgStar_nonneg x hx_mem_Q
  -- Sandwich the pairing between the subgradient lower bound and optimality equality.
  have hsupport : f x ≥ f xStar + inner ℝ gStar (x - xStar) := hsubgrad x
  have hx_le : f x ≤ f xStar := hx_min (mem_constrainedArgmin_iff.mp hxStar).1
  linarith

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: a subgradient certificate at one constrained
minimizer propagates to the whole minimizer set and satisfies the pairwise normal-cone inequalities
there. -/
-- Proof sketch: if `x ∈ argmin[Q] f`, then both `x` and `xStar` minimize `f` on `Q`, so the
-- subgradient inequality at `xStar` together with the nonnegative-pairing condition forces
-- `inner ℝ gStar (x - xStar) = 0`. This identity propagates the subgradient inequality from
-- `xStar` to every minimizer `x`, and the same vanishing pairing gives normal-cone membership at
-- every point of `argmin[Q] f`.
theorem
    subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin
    {Q : Set V} {f : V → ℝ} {xStar gStar : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) :
    gStar ∈
      ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∧
        ∀ x ∈ argmin[Q] f, ∀ y ∈ argmin[Q] f, 0 ≤ inner ℝ gStar (y - x) := by
  have hgStar_sub' := mem_subdifferential_coe_real_iff.mp hgStar_sub
  refine ⟨?_, ?_⟩
  · rw [mem_commonRegularSubdifferential_iff]
    intro x hx
    rw [mem_subdifferential_coe_real_iff]
    have hx_value : f x = f xStar := value_eq_of_mem_argmin hxStar hx
    have hx_pairing : inner ℝ gStar (x - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hx
    -- Transport the affine support inequality from `xStar` to the minimizer `x`.
    intro y
    calc
      f y ≥ f xStar + inner ℝ gStar (y - xStar) := hgStar_sub' y
      _ = f x + inner ℝ gStar (y - x) := by
        rw [displacement_split y x xStar, inner_add_right, hx_pairing, ← hx_value]
        simp
  · intro x hx y hy
    have hx_pairing : inner ℝ gStar (x - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hx
    have hy_pairing : inner ℝ gStar (y - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hy
    -- Re-express the pairwise displacement through `xStar`; both terms vanish separately.
    have hxy : inner ℝ gStar (y - x) = 0 := by
      rw [displacement_difference y x xStar, sub_eq_add_neg, inner_add_right, inner_neg_right,
        hy_pairing, hx_pairing]
      simp
    simp [hxy]

end CommonCertificatePairing

section CommonCertificateOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Consequence for Theorem 3.29 [Chapter3_2.json:34]: a subgradient certificate at one
constrained minimizer propagates to the whole optimal set as a common regular subgradient and a
common normal vector. -/
theorem
    subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin
    {Q : Set V} {f : V → ℝ} {xStar gStar : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) :
    gStar ∈
      ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∩
        NormalCone.common (argmin[Q] f) := by
  -- Reuse the pairing-form propagation theorem and then rewrite the normal-cone owner.
  rcases
      subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin
        hxStar hgStar_sub hgStar_nonneg with
    ⟨hgStar_commonSub, hgStar_pairing⟩
  refine ⟨hgStar_commonSub, ?_⟩
  rw [NormalCone.mem_common_iff_nonneg_pairing]
  intro x hx y hy
  exact hgStar_pairing x hx y hy

/-- Theorem 3.29 [Chapter3_2.json:34]: a feasible point `xStar ∈ Q` belongs to the constrained
optimal set `argmin[Q] f` if and only if there exists a subgradient certificate with nonnegative
pairing on `Q`; every such certificate then belongs to the common regular subdifferential and the
common normal cone of the whole minimizer set. -/
theorem mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing_with_common_certificate
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    (xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) ∧
      ∀ {gStar : V},
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) →
          (∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) →
            gStar ∈
              ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∩
                NormalCone.common (argmin[Q] f) := by
  refine ⟨?_, ?_⟩
  · exact mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing hQ_convex hf_conv hxStar
  · intro gStar hgStar_sub hgStar_nonneg
    -- Recover minimizer membership from the recalled optimality criterion, then propagate the
    -- certificate to the whole minimizer set.
    have hxStar_argmin : xStar ∈ argmin[Q] f :=
      (mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing hQ_convex hf_conv hxStar).2
        ⟨gStar, hgStar_sub, hgStar_nonneg⟩
    exact
      subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin
        hxStar_argmin hgStar_sub hgStar_nonneg

end CommonCertificateOwner
