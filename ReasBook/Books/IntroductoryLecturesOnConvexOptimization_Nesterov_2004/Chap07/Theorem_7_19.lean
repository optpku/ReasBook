/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis
open scoped SeminormDualNorm
open scoped NormalCone
open scoped ConstrainedArgmin

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 7.19 lies in the chapter's strict-positivity / dual-seminorm domain.

Sampled owner-style declarations:
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the nearby Chapter 7 ambient positivity
  predicate written on whole-space subgradients `∂[Set.univ] f(x)`;
- `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` in `Chap02/Definition_2_5`, the project owner
  for the dual norm of a separated seminorm;
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner bridge for real-valued relative subgradients on a feasible set;
- mathlib `ConvexOn.sup`, the canonical convex-max owner for the pointwise maximum of two convex
  functions on the same feasible set.

Best owner abstraction:
- source reference: Definition 7.81's strict-positivity inequality for the augmented objective on
  `Q`;
- source-facing repair: state the labeled theorem on source data `φ : Q → ℝ` and the source
  augmented objective `x ↦ max (φ x) (L * p x)` on `Q`, with a named bridge to the imported
  ambient owner `StrictlyPositiveOn`;
- bridge/view: the file-local constrained comparison predicate `StrictlyPositiveOnWithin Q` and
  the top-extension predicate `StrictlyPositiveOnTopExtension Q`, used only as auxiliary
  comparison owners rather than the main labeled theorem surface;
- core/canonical: `p : Seminorm ℝ E` together with `[Seminorm.IsNorm p]`, the owner map
  `p.dualNorm`, the source-controlled model `φ : E → ℝ`, the Chapter 3 feasible-set
  subgradient surface `g ∈ ∂[Q] φ(x)`, and the constrained and top-extension branch lemmas used
  for local comparison checks.

Primitive data:
- the feasible set `Q`;
- the convex objective `φ : E → ℝ`;
- the separated seminorm `p : Seminorm ℝ E`;
- the scalar bound `L`.

Derived API:
- the dual norm `p.dualNorm`;
- the imported ambient Definition 7.81 owner `StrictlyPositiveOn`;
- the source-side positivity bridge `StrictlyPositiveOnSubtype` from a function `Q → ℝ` to the
  imported ambient owner `StrictlyPositiveOn`;
- the file-local constrained comparison predicate `StrictlyPositiveOnWithin`;
- the file-local top-extension positivity predicate `StrictlyPositiveOnTopExtension`;
- the Chapter 3 constrained subgradient notation `∂[Q] ... (x)`;
- the local constrained helper predicate `StrictlyPositiveOnWithin` and its projection lemma
  `StrictlyPositiveOnWithin.inequality`;
- the local normal-cone and branch lemmas used in constrained and extension-side reductions.

The previous version rebuilt a local `VectorNorm` wrapper and a duplicate dual-norm definition with
the exact same mathematical content as the Chapter 2 owner `Seminorm.dualNorm`. This repair keeps
that cleanup while restoring the labeled theorem to the Definition 7.81 owner through an explicit
equality-on-`Q` bridge; the constrained and top-extension predicates remain available only as local
auxiliary comparison surfaces.
-/

/-- A constrained-subgradient analogue of Definition 7.81 for functions controlled only on a
feasible set `Q`. -/
def StrictlyPositiveOnWithin (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y g : E⦄,
    x ∈ Q →
    y ∈ Q →
    g ∈ ∂[Q] f(x) →
    0 ≤ f y + f x + inner ℝ g (y - x)

/-- A function that is strictly positive on `Q` in the constrained-subgradient sense satisfies the
defining inequality at every pair of feasible points and every feasible subgradient. -/
theorem StrictlyPositiveOnWithin.inequality
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOnWithin Q f)
    {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q) (hg : g ∈ ∂[Q] f(x)) :
    0 ≤ f y + f x + inner ℝ g (y - x) := by
  simpa [StrictlyPositiveOnWithin] using hf hx hy hg

/-- The canonical `⊤`-extension of a real-valued function restricted to a feasible set `Q`. -/
noncomputable def topExtensionOn (Q : Set E) (f : E → ℝ) : E → WithTop ℝ := by
  classical
  exact fun z : E ↦ if z ∈ Q then ((f z : ℝ) : WithTop ℝ) else ⊤

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem topExtensionOn_apply_of_mem
    {Q : Set E} {f : E → ℝ} {z : E} (hz : z ∈ Q) :
    topExtensionOn Q f z = ((f z : ℝ) : WithTop ℝ) := by
  classical
  simp [topExtensionOn, hz]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem topExtensionOn_apply_of_not_mem
    {Q : Set E} {f : E → ℝ} {z : E} (hz : z ∉ Q) :
    topExtensionOn Q f z = ⊤ := by
  classical
  simp [topExtensionOn, hz]

/-- A source-faithful top-extension version of Definition 7.81 for functions specified only on a
feasible set `Q`. -/
def StrictlyPositiveOnTopExtension (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y g : E⦄,
    x ∈ Q →
    y ∈ Q →
    g ∈ ∂ (topExtensionOn Q f)(x) →
    0 ≤ f y + f x + inner ℝ g (y - x)

/-- A function that is strictly positive on `Q` in the top-extension sense satisfies the defining
inequality at every pair of feasible points and every top-extension subgradient. -/
theorem StrictlyPositiveOnTopExtension.inequality
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOnTopExtension Q f)
    {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q) (hg : g ∈ ∂ (topExtensionOn Q f)(x)) :
    0 ≤ f y + f x + inner ℝ g (y - x) := by
  -- Apply the defining top-extension positivity inequality to the chosen feasible data.
  simpa [StrictlyPositiveOnTopExtension] using hf hx hy hg

-- Proof sketch: prove the feasible-set strict-positivity inequality for constrained subgradients
-- of `fun z ↦ max (φ z) (L * p z)` using the feasible-set dual-norm control on `φ` together with
-- the branch-local max-subgradient lemmas already developed in this file.
/-- Helper for Theorem 7.19: once a subgradient has dual norm at most `L`, the strict-positivity
expression is controlled by the two seminorm branches of the max objective. -/
lemma strictly_positive_expr_nonneg_of_dualNorm_le
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) {x y g : E}
    (hg_dual : p.dualNorm g ≤ L) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  have hinner_neg :
      -inner ℝ g (y - x) ≤ p.dualNorm g * p (y - x) := by
    -- Apply dual Cauchy to `-g` so the sign on the pairing matches the target expression.
    have hle :
        inner ℝ (-g) (y - x) ≤ p.dualNorm (-g) * p (y - x) :=
      Seminorm.inner_le_dualNorm_mul p (y - x) (-g)
    have hdual_neg : p.dualNorm (-g) = p.dualNorm g := by
      rw [Seminorm.dualNorm_apply, Seminorm.dualNorm_apply]
      congr 1
      ext r
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨-u, ?_, ?_⟩
        · simpa [Set.mem_setOf_eq, map_neg_eq_map] using hu
        · simp [inner_neg_left]
      · rintro ⟨u, hu, rfl⟩
        refine ⟨-u, ?_, ?_⟩
        · simpa [Set.mem_setOf_eq, map_neg_eq_map] using hu
        · simp [inner_neg_left]
    simpa [inner_neg_left, hdual_neg] using hle
  have htriangle : p (y - x) ≤ p y + p x := by
    -- The seminorm of a difference is bounded by the sum of the endpoint seminorms.
    simpa [sub_eq_add_neg, map_neg_eq_map] using map_add_le_add p y (-x)
  have hdual_nonneg : 0 ≤ p.dualNorm g := by
    -- The dual norm is the supremum of pairings over the closed unit ball, which contains `0`.
    have hupper :
        BddAbove ((fun z : E ↦ inner ℝ g z) '' {z | p z ≤ 1}) := by
      obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
      refine ⟨‖g‖ * C, ?_⟩
      rintro r ⟨z, hz, rfl⟩
      have hz_p : p z ≤ 1 := by
        simpa using hz
      have hz_norm : ‖z‖ ≤ C := by
        calc
          ‖z‖ ≤ C * p z := hnorm_le z
          _ ≤ C * 1 := by
            exact mul_le_mul_of_nonneg_left hz_p hC_pos.le
          _ = C := by ring
      calc
        inner ℝ g z ≤ ‖g‖ * ‖z‖ := real_inner_le_norm _ _
        _ ≤ ‖g‖ * C := by
          gcongr
    rw [Seminorm.dualNorm_apply]
    exact le_csSup hupper ⟨0, by simp [map_zero p]⟩
  have hbound :
      p.dualNorm g * p (y - x) ≤ L * p y + L * p x := by
    calc
      p.dualNorm g * p (y - x) ≤ p.dualNorm g * (p y + p x) := by
        exact mul_le_mul_of_nonneg_left htriangle hdual_nonneg
      _ ≤ L * (p y + p x) := by
        exact mul_le_mul_of_nonneg_right hg_dual (add_nonneg (apply_nonneg p y) (apply_nonneg p x))
      _ = L * p y + L * p x := by ring
  have hy_branch : L * p y ≤ max (φ y) (L * p y) := le_max_right _ _
  have hx_branch : L * p x ≤ max (φ x) (L * p x) := le_max_right _ _
  linarith [hinner_neg, hbound, hy_branch, hx_branch]

/-- Helper for Theorem 7.19: the scaled seminorm branch remains positively homogeneous of
degree `1` on the whole space. -/
lemma scaled_seminorm_isPositivelyHomogeneousOn_univ
    (p : Seminorm ℝ E) (L : ℝ) :
    IsPositivelyHomogeneousOn 1 Set.univ (fun z : E ↦ L * p z) := by
  refine ⟨?_, ?_⟩
  · intro z hz τ
    simp
  · intro z hz τ
    -- Rewrite the seminorm scaling law into the positive-homogeneity owner interface.
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul, mul_left_comm, mul_assoc] using
      congrArg (fun r : ℝ ↦ L * r) (map_smul_eq_mul p (τ : ℝ) z)

/-- Helper for Theorem 7.19: every subgradient of the scaled seminorm branch has dual norm at
most the scaling factor `L`. -/
lemma dualNorm_le_of_mem_subdifferential_scaled_seminorm
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (L : ℝ) (hL_nonneg : 0 ≤ L) {x g : E}
    (hg : g ∈ ∂ (fun z ↦ (((L * p z) : ℝ) : WithTop ℝ))(x)) :
    p.dualNorm g ≤ L := by
  have hhom :
      IsPositivelyHomogeneousOn 1 Set.univ (fun z : E ↦ L * p z) :=
    scaled_seminorm_isPositivelyHomogeneousOn_univ p L
  have hg_zero : g ∈ ∂ (fun z ↦ (((L * p z) : ℝ) : WithTop ℝ))(0) := by
    -- One-homogeneity moves every subgradient back to the origin owner.
    rw [subdifferential_eq_subdifferential_zero_of_posHomogeneous hhom x] at hg
    exact hg.1
  have hsupport : ∀ z : E, inner ℝ g z ≤ L * p z := by
    -- At the origin, the subgradient inequality is exactly the dual-pairing upper bound.
    intro z
    have hz := mem_subdifferential_coe_real_iff.mp hg_zero z
    simpa [map_zero p] using hz
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp [map_zero p], by simp⟩⟩
  · rintro r ⟨z, hz, rfl⟩
    have hz_support : inner ℝ g z ≤ L * p z := hsupport z
    have hz_ball : p z ≤ 1 := hz
    calc
      inner ℝ g z ≤ L * p z := hz_support
      _ ≤ L * 1 := by
        gcongr
      _ = L := by ring

/-- Helper for Theorem 7.19: a whole-space subgradient of the scaled seminorm branch attains the
base value at the base point. -/
lemma inner_eq_scaledSeminorm_at_base_of_mem_subdifferential_scaled_seminorm
    (p : Seminorm ℝ E) (L : ℝ)
    {x g : E}
    (hg : g ∈ ∂ (fun z ↦ (((L * p z) : ℝ) : WithTop ℝ))(x)) :
    inner ℝ g x = L * p x := by
  have hsupport := mem_subdifferential_coe_real_iff.mp hg
  have hzero :
      L * p (0 : E) ≥ L * p x + inner ℝ g ((0 : E) - x) := hsupport 0
  have hbase_le : L * p x ≤ inner ℝ g x := by
    -- Test the support inequality at the origin to recover the lower bound at `x`.
    simpa [map_zero p, sub_eq_add_neg, inner_neg_right] using hzero
  have hdouble :
      L * p ((2 : ℝ) • x) ≥ L * p x + inner ℝ g (((2 : ℝ) • x) - x) :=
    hsupport ((2 : ℝ) • x)
  have hinner_le : inner ℝ g x ≤ L * p x := by
    -- Test once more at `2 • x` and simplify the positively homogeneous branch.
    have hdouble' :
        2 * (L * p x) ≥ L * p x + inner ℝ g x := by
      calc
        2 * (L * p x) = L * p ((2 : ℝ) • x) := by
          rw [map_smul_eq_mul]
          rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        _ ≥ L * p x + inner ℝ g (((2 : ℝ) • x) - x) := hdouble
        _ = L * p x + inner ℝ g x := by
          simp [sub_eq_add_neg, two_smul]
    linarith
  exact le_antisymm hinner_le hbase_le

/-- Helper for Theorem 7.19: the `p`-dual norm stays bounded by `L` under convex combinations of
two vectors whose `p`-dual norms are already bounded by `L`. -/
lemma dualNorm_le_of_convexCombination
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (L α : ℝ) (hL_nonneg : 0 ≤ L) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    {g₁ g₂ : E}
    (hg₁ : p.dualNorm g₁ ≤ L) (hg₂ : p.dualNorm g₂ ≤ L) :
    p.dualNorm (α • g₁ + (1 - α) • g₂) ≤ L := by
  have hα'_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα_le_one
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp [map_zero p], by simp⟩⟩
  · rintro r ⟨z, hz, rfl⟩
    have hz_nonneg : 0 ≤ p z := apply_nonneg p z
    have hterm₁ :
        α * inner ℝ g₁ z ≤ α * (L * 1) := by
      have hscale :
          α * inner ℝ g₁ z ≤ α * (p.dualNorm g₁ * p z) :=
        mul_le_mul_of_nonneg_left (Seminorm.inner_le_dualNorm_mul p z g₁) hα_nonneg
      have hbound :
          α * (p.dualNorm g₁ * p z) ≤ α * (L * 1) := by
        have hright :
            p.dualNorm g₁ * p z ≤ L * 1 := by
          calc
            p.dualNorm g₁ * p z ≤ L * p z := by
              exact mul_le_mul_of_nonneg_right hg₁ hz_nonneg
            _ ≤ L * 1 := by
              exact mul_le_mul_of_nonneg_left hz hL_nonneg
        exact mul_le_mul_of_nonneg_left hright hα_nonneg
      exact hscale.trans hbound
    have hterm₂ :
        (1 - α) * inner ℝ g₂ z ≤ (1 - α) * (L * 1) := by
      have hscale :
          (1 - α) * inner ℝ g₂ z ≤ (1 - α) * (p.dualNorm g₂ * p z) :=
        mul_le_mul_of_nonneg_left (Seminorm.inner_le_dualNorm_mul p z g₂) hα'_nonneg
      have hbound :
          (1 - α) * (p.dualNorm g₂ * p z) ≤ (1 - α) * (L * 1) := by
        have hright :
            p.dualNorm g₂ * p z ≤ L * 1 := by
          calc
            p.dualNorm g₂ * p z ≤ L * p z := by
              exact mul_le_mul_of_nonneg_right hg₂ hz_nonneg
            _ ≤ L * 1 := by
              exact mul_le_mul_of_nonneg_left hz hL_nonneg
        exact mul_le_mul_of_nonneg_left hright hα'_nonneg
      exact hscale.trans hbound
    -- Expand the pairing of the convex combination and combine the two branch bounds.
    have hpairing :
        inner ℝ (α • g₁ + (1 - α) • g₂) z =
          α * inner ℝ g₁ z + (1 - α) * inner ℝ g₂ z := by
      simp [inner_add_left, inner_smul_left]
    -- Put the pairing into scalar form so the two branch bounds combine by linear arithmetic.
    have hterms :
        α * inner ℝ g₁ z + (1 - α) * inner ℝ g₂ z ≤
          α * (L * 1) + (1 - α) * (L * 1) := by
      exact add_le_add hterm₁ hterm₂
    have hbound' :
        α * inner ℝ g₁ z + (1 - α) * inner ℝ g₂ z ≤ L := by
      calc
        α * inner ℝ g₁ z + (1 - α) * inner ℝ g₂ z
            ≤ α * (L * 1) + (1 - α) * (L * 1) := hterms
        _ = L := by ring
    simpa [hpairing] using hbound'

/-- Helper for Theorem 7.19: a whole-space subgradient restricts to any feasible-set
subgradient at the same base point. -/
lemma mem_subdifferentialWithin_of_mem_subdifferential
    (Q : Set E) {f : E → ℝ} {x g : E}
    (hx : x ∈ Q)
    (hg : g ∈ ∂[Set.univ] f(x)) :
    g ∈ ∂[Q] f(x) := by
  -- Rewrite both owners to the same affine lower-support inequality and forget the points
  -- outside the feasible set.
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  rcases hg with ⟨-, hsubgrad⟩
  refine ⟨hx, ?_⟩
  intro y hy
  exact hsubgrad (by simp)

/-- Helper for Theorem 7.19: the scaled seminorm branch is convex on every convex feasible set. -/
lemma convexOn_scaledSeminorm
    (Q : Set E) (p : Seminorm ℝ E) (L : ℝ) (hQ_convex : Convex ℝ Q) (hL_nonneg : 0 ≤ L) :
    ConvexOn ℝ Q (fun z : E ↦ L * p z) := by
  -- A nonnegative scalar preserves convexity of the seminorm branch.
  simpa [smul_eq_mul] using ((p.convexOn).smul hL_nonneg).subset (by simp) hQ_convex

/-- Helper for Theorem 7.19: subtracting a normal-cone vector preserves feasible subgradients on
`Q`. -/
lemma sub_mem_subdifferentialWithin_of_mem_normalCone
    [CompleteSpace E]
    (Q : Set E) (f : E → ℝ) {x g n : E}
    (hg : g ∈ ∂[Q] f(x)) (hn : n ∈ N[Q] x) :
    g - n ∈ ∂[Q] f(x) := by
  -- Route correction: with this file's sign convention for `N[Q] x`, subtracting the normal-cone
  -- vector weakens the affine support inequality and therefore preserves feasible subgradients.
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  rcases hg with ⟨hx, hsubgrad⟩
  refine ⟨hx, ?_⟩
  intro y hy
  have hnormal : 0 ≤ inner ℝ n (y - x) := (mem_normalCone_iff.mp hn) y hy
  have hsupport : f y ≥ f x + inner ℝ g (y - x) := hsubgrad hy
  -- Combine the original support inequality with the nonnegative normal-cone pairing.
  calc
    f y ≥ f x + inner ℝ g (y - x) := hsupport
    _ ≥ f x + (inner ℝ g (y - x) - inner ℝ n (y - x)) := by linarith
    _ = f x + inner ℝ (g - n) (y - x) := by
      simp [sub_eq_add_neg, inner_add_left]

/-- Helper for Theorem 7.19: if the difference `g₁ - g₂` lies in the normal cone at `x`,
then the corresponding pairing along every feasible displacement from `x` is larger for `g₁`
than for `g₂`. -/
lemma inner_le_of_sub_mem_normalCone
    [CompleteSpace E]
    (Q : Set E) {x y g₁ g₂ : E}
    (hy : y ∈ Q) (hnormal : g₁ - g₂ ∈ N[Q] x) :
    inner ℝ g₂ (y - x) ≤ inner ℝ g₁ (y - x) := by
  -- Expand the normal-cone inequality once, then rewrite the difference pairing.
  have hpair_nonneg : 0 ≤ inner ℝ (g₁ - g₂) (y - x) :=
    (mem_normalCone_iff.mp hnormal) y hy
  simpa [sub_eq_add_neg, inner_add_left] using hpair_nonneg

/-- Helper for Theorem 7.19: once one feasible subgradient set is uniformly `L`-bounded in the
`p`-dual norm, its normal cone must be trivial. -/
lemma eq_zero_of_mem_normalCone_of_bounded_subdifferentialWithin
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (Q : Set E) (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (f : E → ℝ) (L : ℝ) {x g n : E}
    (hg : g ∈ ∂[Q] f(x)) (hn : n ∈ N[Q] x)
    (hbound : ∀ ⦃g' : E⦄, g' ∈ ∂[Q] f(x) → p.dualNorm g' ≤ L) :
    n = 0 := by
  by_contra hn_ne
  have hnorm_sq_pos : 0 < ‖n‖ ^ (2 : ℕ) := by
    have hnorm_pos : 0 < ‖n‖ := norm_pos_iff.mpr hn_ne
    nlinarith
  have hnorm_sq_ne : ‖n‖ ^ (2 : ℕ) ≠ 0 := by
    exact ne_of_gt hnorm_sq_pos
  let A : ℝ := L * p n + inner ℝ g n
  let t : ℝ := (|A| + 1) / ‖n‖ ^ (2 : ℕ)
  have ht_nonneg : 0 ≤ t := by
    refine div_nonneg ?_ (show 0 ≤ ‖n‖ ^ (2 : ℕ) by positivity)
    positivity
  have htn : t • n ∈ N[Q] x := by
    rw [mem_normalCone_iff]
    intro y hy
    have hnormal : 0 ≤ inner ℝ n (y - x) := (mem_normalCone_iff.mp hn) y hy
    simpa [inner_smul_left] using mul_nonneg ht_nonneg hnormal
  have hsub : g - t • n ∈ ∂[Q] f(x) :=
    sub_mem_subdifferentialWithin_of_mem_normalCone Q f hg htn
  have hdual : p.dualNorm (g - t • n) ≤ L := hbound hsub
  have hinner :
      inner ℝ (g - t • n) (-n) ≤ L * p (-n) := by
    calc
      inner ℝ (g - t • n) (-n) ≤ p.dualNorm (g - t • n) * p (-n) :=
        Seminorm.inner_le_dualNorm_mul p (-n) (g - t • n)
      _ ≤ L * p (-n) := by
        exact mul_le_mul_of_nonneg_right hdual (apply_nonneg p (-n))
  have ht_mul :
      t * ‖n‖ ^ (2 : ℕ) = |A| + 1 := by
    dsimp [t]
    field_simp [hnorm_sq_ne]
  have hineq : |A| + 1 ≤ A := by
    -- Expand the tested pairing against `-n` and isolate the large-`t` term.
    have hinner' :
        -inner ℝ g n + t * ‖n‖ ^ (2 : ℕ) ≤ L * p n := by
      simpa [A, t, map_neg_eq_map, sub_eq_add_neg, inner_add_left, inner_neg_right,
        inner_smul_left, real_inner_self_eq_norm_sq, add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg] using hinner
    linarith [hinner', ht_mul]
  have hA_le_abs : A ≤ |A| := le_abs_self A
  linarith

/-- Helper for Theorem 7.19: for a globally convex objective, a feasible subgradient already is a
whole-space subgradient once the normal cone at the base point is trivial. -/
lemma mem_subdifferential_of_mem_subdifferentialWithin_of_trivialNormalCone
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (Q : Set E) {f : E → ℝ}
    (hQ_convex : Convex ℝ Q) (hf_conv : ConvexOn ℝ Set.univ f)
    {x g : E} (hgQ : g ∈ ∂[Q] f(x))
    (hNormalZero : ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0) :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) := by
  let k : E → ℝ := fun z ↦ f z - inner ℝ g z
  have hx : x ∈ Q := (mem_subdifferentialWithin_iff.mp hgQ).1
  have hlinear : ConvexOn ℝ Set.univ (fun z ↦ -inner ℝ g z) := by
    let ℓ : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E 0 + ((innerSL ℝ (-g)).toLinearMap).toAffineMap
    have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
      simpa [Function.comp, ℓ] using (convexOn_id convex_univ).comp_affineMap ℓ
    refine ⟨convex_univ, ?_⟩
    intro z hz w hw a b ha hb hab
    simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
      hℓ.2 (by simp) (by simp) ha hb hab
  have hk_conv : ConvexOn ℝ Set.univ k := by
    simpa [k, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hf_conv.add hlinear
  have hx_argmin : x ∈ argmin[Q] k := by
    rw [mem_constrainedArgmin_iff]
    refine ⟨hx, isMinOn_iff.mpr ?_⟩
    intro y hy
    have hsupport :
        f y ≥ f x + inner ℝ g (y - x) := (mem_subdifferentialWithin_iff.mp hgQ).2 hy
    have hk_support : k x ≤ k y := by
      dsimp [k]
      have hinner : inner ℝ g (y - x) = inner ℝ g y - inner ℝ g x := by
        simp [sub_eq_add_neg, inner_add_right]
      rw [hinner] at hsupport
      linarith
    exact hk_support
  rcases (mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone
      hQ_convex hk_conv hx).mp hx_argmin with ⟨n, hnsub, hnQ⟩
  have hn_zero : n = 0 := hNormalZero hnQ
  have hzero_sub : (0 : E) ∈ ∂ (fun y ↦ (k y : WithTop ℝ))(x) := by
    simpa [hn_zero] using hnsub
  rw [mem_subdifferential_coe_real_iff]
  intro y
  have hk_support : k y ≥ k x := by
    simpa using (mem_subdifferential_coe_real_iff.mp hzero_sub) y
  -- Expand the tilted objective once to recover the original affine support inequality for `f`.
  dsimp [k] at hk_support
  have hinner : inner ℝ g (y - x) = inner ℝ g y - inner ℝ g x := by
    simp [sub_eq_add_neg, inner_add_right]
  rw [hinner]
  linarith

/-- Helper for Theorem 7.19: on a trivial normal cone, a constrained subgradient of the scaled
seminorm branch is automatically a whole-space subgradient, so the global dual-norm bound applies.
-/
lemma dualNorm_le_of_mem_subdifferentialWithin_scaledSeminorm
    [FiniteDimensional ℝ E]
    (Q : Set E) (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (L : ℝ) (hQ_convex : Convex ℝ Q) (hL_nonneg : 0 ≤ L)
    {x g : E}
    (hgQ : g ∈ ∂[Q] ((fun z ↦ L * p z) : E → ℝ)(x))
    (hNormalZero : ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0) :
    p.dualNorm g ≤ L := by
  have hg :
      g ∈ ∂ (fun z ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ))(x) :=
    mem_subdifferential_of_mem_subdifferentialWithin_of_trivialNormalCone
      Q hQ_convex (by
        simpa [smul_eq_mul] using (p.convexOn).smul hL_nonneg) hgQ hNormalZero
  -- Once the constrained owner collapses to the whole-space owner, reuse the existing bound.
  simpa using dualNorm_le_of_mem_subdifferential_scaled_seminorm p L hL_nonneg hg

/-- Helper for Theorem 7.19: if the left branch is active at `x`, then every feasible
subgradient of the left branch is also a feasible subgradient of the pointwise max. -/
lemma mem_subdifferentialWithin_max_of_mem_left_branch
    (Q : Set E) {f ψ : E → ℝ} {x g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hactive : ψ x ≤ f x) :
    g ∈ ∂[Q] ((fun z ↦ max (f z) (ψ z)) : E → ℝ) (x) := by
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  rcases hg with ⟨hx, hsupport⟩
  refine ⟨hx, ?_⟩
  intro y hy
  -- Compare the active left branch at `x` with the ambient max objective.
  calc
    max (f y) (ψ y) ≥ f y := le_max_left _ _
    _ ≥ f x + inner ℝ g (y - x) := hsupport hy
    _ = max (f x) (ψ x) + inner ℝ g (y - x) := by
      rw [max_eq_left hactive]

/-- Helper for Theorem 7.19: if the right branch is active at `x`, then every feasible
subgradient of the right branch is also a feasible subgradient of the pointwise max. -/
lemma mem_subdifferentialWithin_max_of_mem_right_branch
    (Q : Set E) {f ψ : E → ℝ} {x g : E}
    (hg : g ∈ ∂[Q] ψ(x))
    (hactive : f x ≤ ψ x) :
    g ∈ ∂[Q] ((fun z ↦ max (f z) (ψ z)) : E → ℝ) (x) := by
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  rcases hg with ⟨hx, hsupport⟩
  refine ⟨hx, ?_⟩
  intro y hy
  -- Compare the active right branch at `x` with the ambient max objective.
  calc
    max (f y) (ψ y) ≥ ψ y := le_max_right _ _
    _ ≥ ψ x + inner ℝ g (y - x) := hsupport hy
    _ = max (f x) (ψ x) + inner ℝ g (y - x) := by
      rw [max_eq_right hactive]

/-- Helper for Theorem 7.19: if the right branch is active at `x`, then every whole-space
subgradient of the right branch is also a whole-space subgradient of the pointwise max. -/
lemma mem_subdifferential_max_of_mem_right_branch
    {f ψ : E → ℝ} {x g : E}
    (hg : g ∈ ∂ (fun z ↦ (((ψ z) : ℝ) : WithTop ℝ))(x))
    (hactive : f x ≤ ψ x) :
    g ∈ ∂ (fun z ↦ (((max (f z) (ψ z)) : ℝ) : WithTop ℝ))(x) := by
  rw [mem_subdifferential_coe_real_iff] at hg ⊢
  intro y
  -- Compare the active right branch support inequality with the larger max objective.
  calc
    max (f y) (ψ y) ≥ ψ y := le_max_right _ _
    _ ≥ ψ x + inner ℝ g (y - x) := hg y
    _ = max (f x) (ψ x) + inner ℝ g (y - x) := by
      rw [max_eq_right hactive]

/-- Helper for Theorem 7.19: at a tie point, every convex combination of feasible branch
subgradients is again a feasible subgradient of the max objective. -/
lemma convexCombination_mem_subdifferentialWithin_max_of_eq
    (Q : Set E) {f ψ : E → ℝ} {x gf gψ : E} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hEq : f x = ψ x)
    (hgf : gf ∈ ∂[Q] f(x))
    (hgψ : gψ ∈ ∂[Q] ψ(x)) :
    α • gf + (1 - α) • gψ ∈ ∂[Q] ((fun z ↦ max (f z) (ψ z)) : E → ℝ) (x) := by
  rw [mem_subdifferentialWithin_iff] at hgf hgψ ⊢
  rcases hgf with ⟨hx, hsupportf⟩
  rcases hgψ with ⟨-, hsupportψ⟩
  refine ⟨hx, ?_⟩
  intro y hy
  have hα'_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα_le_one
  have hf_scaled :
      α * (f x + inner ℝ gf (y - x)) ≤ α * f y := by
    exact mul_le_mul_of_nonneg_left (hsupportf hy) hα_nonneg
  have hψ_scaled :
      (1 - α) * (ψ x + inner ℝ gψ (y - x)) ≤ (1 - α) * ψ y := by
    exact mul_le_mul_of_nonneg_left (hsupportψ hy) hα'_nonneg
  have hcombo_le :
      α * (f x + inner ℝ gf (y - x)) +
          (1 - α) * (ψ x + inner ℝ gψ (y - x)) ≤
        α * f y + (1 - α) * ψ y := by
    exact add_le_add hf_scaled hψ_scaled
  -- The max dominates every convex combination of the two branch values at `y`.
  have hbranch_le :
      α * f y + (1 - α) * ψ y ≤ max (f y) (ψ y) := by
    calc
      α * f y + (1 - α) * ψ y
          ≤ α * max (f y) (ψ y) + (1 - α) * max (f y) (ψ y) := by
            gcongr
            · exact le_max_left _ _
            · exact le_max_right _ _
      _ = max (f y) (ψ y) := by ring
  -- Rewrite the left-hand side into the target affine support inequality for the convex
  -- combination of the two branch subgradients.
  have hcombo_eq :
      α * (f x + inner ℝ gf (y - x)) +
          (1 - α) * (ψ x + inner ℝ gψ (y - x)) =
        max (f x) (ψ x) + inner ℝ (α • gf + (1 - α) • gψ) (y - x) := by
    -- Normalize the pairing of the convex combination before the final arithmetic identity.
    have hpair :
        inner ℝ (α • gf + (1 - α) • gψ) (y - x) =
          α * inner ℝ gf (y - x) + (1 - α) * inner ℝ gψ (y - x) := by
      simp [inner_add_left, inner_smul_left]
    rw [hEq, max_eq_left le_rfl, hpair]
    ring
  -- Combine the scaled branch inequalities with the max domination at `y`.
  calc
    max (f y) (ψ y)
        ≥ α * f y + (1 - α) * ψ y := hbranch_le
    _ ≥ α * (f x + inner ℝ gf (y - x)) +
          (1 - α) * (ψ x + inner ℝ gψ (y - x)) := hcombo_le
    _ = max (f x) (ψ x) + inner ℝ (α • gf + (1 - α) • gψ) (y - x) := hcombo_eq

/-- Helper for Theorem 7.19: on a strict-left branch, a feasible subgradient of the max already
is a feasible subgradient of the left branch. -/
lemma mem_subdifferentialWithin_left_of_mem_max_strictLeft
    (Q : Set E) {f ψ : E → ℝ} {x g : E}
    (hQ_convex : Convex ℝ Q)
    (hf_conv : ConvexOn ℝ Q f) (hψ_conv : ConvexOn ℝ Q ψ)
    (hg : g ∈ ∂[Q] ((fun z : E ↦ max (f z) (ψ z)) : E → ℝ) (x))
    (hactive : ψ x < f x) :
    g ∈ ∂[Q] f(x) := by
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  rcases hg with ⟨hx, hsupportMax⟩
  refine ⟨hx, ?_⟩
  intro y hy
  let γ : ℝ := inner ℝ g (y - x)
  by_contra hyf
  have hyf_lt : f y < f x + γ := by
    exact not_le.mp hyf
  let a : ℝ := f x - ψ x
  have ha_pos : 0 < a := sub_pos.mpr hactive
  let c : ℝ := max (ψ y - ψ x - γ) 0
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact le_max_right _ _
  let t : ℝ := min (1 / 2 : ℝ) (a / (2 * (c + 1)))
  have hc1_pos : 0 < c + 1 := by
    linarith
  have ht_pos : 0 < t := by
    refine lt_min ?_ ?_
    · norm_num
    · refine div_pos ha_pos ?_
      positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le_one : t ≤ 1 := by
    calc
      t ≤ (1 / 2 : ℝ) := min_le_left _ _
      _ ≤ 1 := by norm_num
  have hxt_mem : (1 - t) • x + t • y ∈ Q := by
    exact hQ_convex hx hy (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
  have hmax_support := hsupportMax hxt_mem
  have hbase : max (f x) (ψ x) = f x := by
    rw [max_eq_left (le_of_lt hactive)]
  have hinner :
      inner ℝ g (((1 - t) • x + t • y) - x) = t * γ := by
    calc
      inner ℝ g (((1 - t) • x + t • y) - x)
          = inner ℝ g ((1 - t) • x + t • y) - inner ℝ g x := by
              rw [inner_sub_right]
      _ = (1 - t) * inner ℝ g x + t * inner ℝ g y - inner ℝ g x := by
            simp [inner_add_right, inner_smul_right]
      _ = t * (inner ℝ g y - inner ℝ g x) := by ring
      _ = t * inner ℝ g (y - x) := by
            rw [inner_sub_right]
      _ = t * γ := by
            rfl
  have hmax_lower :
      f x + t * γ ≤ max (f ((1 - t) • x + t • y)) (ψ ((1 - t) • x + t • y)) := by
    rw [hbase, hinner] at hmax_support
    exact hmax_support
  have hf_upper :
      f ((1 - t) • x + t • y) < f x + t * γ := by
    have hconv := hf_conv.2 hx hy (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
    calc
      f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y := hconv
      _ < (1 - t) * f x + t * (f x + γ) := by
        gcongr
      _ = f x + t * γ := by ring
  have ht_mul_c_le_half :
      t * (c + 1) ≤ a / 2 := by
    have ht_le : t ≤ a / (2 * (c + 1)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right ht_le hc1_pos.le
    have hcalc : (a / (2 * (c + 1))) * (c + 1) = a / 2 := by
      field_simp [hc1_pos.ne']
    simpa [hcalc] using hmul
  have htc_lt_a : t * c < a := by
    have htc_lt_half : t * c < a / 2 := by
      calc
        t * c < t * (c + 1) := by
          nlinarith [ht_pos, hc_nonneg]
        _ ≤ a / 2 := ht_mul_c_le_half
    linarith
  have hψ_upper :
      ψ ((1 - t) • x + t • y) < f x + t * γ := by
    have hconv := hψ_conv.2 hx hy (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
    have hc_bound : ψ y - ψ x - γ ≤ c := by
      dsimp [c]
      exact le_max_left _ _
    calc
      ψ ((1 - t) • x + t • y) ≤ (1 - t) * ψ x + t * ψ y := hconv
      _ = ψ x + t * (ψ y - ψ x) := by ring
      _ ≤ ψ x + t * (γ + c) := by
        nlinarith
      _ < f x + t * γ := by
        linarith
  have hmax_upper :
      max (f ((1 - t) • x + t • y)) (ψ ((1 - t) • x + t • y)) < f x + t * γ := by
    exact max_lt_iff.mpr ⟨hf_upper, hψ_upper⟩
  linarith

/-- Helper for Theorem 7.19: on a strict-right branch, a feasible subgradient of the max already
is a feasible subgradient of the right branch. -/
lemma mem_subdifferentialWithin_right_of_mem_max_strictRight
    (Q : Set E) {f ψ : E → ℝ} {x g : E}
    (hQ_convex : Convex ℝ Q)
    (hf_conv : ConvexOn ℝ Q f) (hψ_conv : ConvexOn ℝ Q ψ)
    (hg : g ∈ ∂[Q] ((fun z : E ↦ max (f z) (ψ z)) : E → ℝ) (x))
    (hactive : f x < ψ x) :
    g ∈ ∂[Q] ψ(x) := by
  -- Swap the two branches and reuse the strict-left reverse implication.
  have hg' : g ∈ ∂[Q] ((fun z : E ↦ max (ψ z) (f z)) : E → ℝ) (x) := by
    simpa [max_comm] using hg
  simpa [max_comm] using
    mem_subdifferentialWithin_left_of_mem_max_strictLeft
      Q hQ_convex hψ_conv hf_conv hg' hactive

/-- Helper for Theorem 7.19: on the strict-right branch, a feasible max-subgradient can be
viewed as an ambient scaled-seminorm subgradient plus a normal-cone remainder. -/
lemma exists_scaledSeminormSubgradient_of_strictRight
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (Q : Set E) (p : Seminorm ℝ E) (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} (hx : x ∈ Q)
    (hQ_convex : Convex ℝ Q) (hφ_conv : ConvexOn ℝ Q φ)
    (hstrictRight : φ x < L * p x)
    (hgQ : g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    ∃ gψ : E,
      gψ ∈ ∂ (fun z : E ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ))(x) ∧
        gψ - g ∈ N[Q] x := by
  let ψTop : E → WithTop ℝ := fun z ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ)
  have hψ_conv : ConvexOn ℝ Q (fun z : E ↦ L * p z) :=
    convexOn_scaledSeminorm Q p L hQ_convex hL_nonneg
  -- First isolate the active right branch on the constrained owner.
  have hgψQ : g ∈ ∂[Q] ((fun z : E ↦ L * p z) : E → ℝ)(x) :=
    mem_subdifferentialWithin_right_of_mem_max_strictRight
      Q hQ_convex hφ_conv hψ_conv hgQ hstrictRight
  have hdom_univ : dom ψTop = Set.univ := by
    ext z
    rw [mem_withTopEffectiveDomain_iff]
    simpa [ψTop] using (WithTop.coe_lt_top (L * p z))
  have hψ_conv_univ :
      ConvexOn ℝ (dom ψTop) (withTopRealPart ψTop) := by
    rw [hdom_univ]
    simpa [ψTop] using
      ((p.convexOn).smul hL_nonneg : ConvexOn ℝ Set.univ (fun z : E ↦ L * p z))
  have hψ_conv_Q :
      ConvexOn ℝ Q (withTopRealPart ψTop) := by
    simpa [ψTop] using hψ_conv
  have hQ_subset_interior : Q ⊆ interior (dom ψTop) := by
    intro z hz
    rw [hdom_univ]
    simp
  -- Then use the canonical constrained-to-ambient normal-cone decomposition theorem.
  rcases existsSubgradientWithNormalConeRemainderOfMemConstrainedSubdifferential
      hψ_conv_univ hψ_conv_Q hQ_subset_interior hx
      (by simpa using hgψQ) with
    ⟨gψ, hgψ, hnormal⟩
  exact ⟨gψ, hgψ, hnormal⟩

/-- Helper for Theorem 7.19: a Slater ball around `x` gives a feasible subgradient of a convex
real-valued function on `Q` at `x`. -/
lemma subdifferentialWithinNonemptyOfBall
    [FiniteDimensional ℝ E]
    (Q : Set E) {f : E → ℝ}
    (hf_conv : ConvexOn ℝ Q f)
    {x : E} {ε : ℝ} (hε : 0 < ε) (hball : Metric.ball x ε ⊆ Q) :
    (∂[Q] f(x)).Nonempty := by
  -- The real-valued objective has full domain, so the Slater-center owner theorem applies
  -- directly to the `WithTop ℝ` coercion of `f`.
  have hdom_univ : dom (fun y : E ↦ ((f y : ℝ) : WithTop ℝ)) = Set.univ := by
    ext y
    simp [mem_withTopEffectiveDomain_iff]
  have hQ_subset_interior :
      Q ⊆ interior (dom (fun y : E ↦ ((f y : ℝ) : WithTop ℝ))) := by
    intro y hy
    simpa [hdom_univ] using (show y ∈ interior (Set.univ : Set E) by simp)
  have hconv_withTop :
      ConvexOn ℝ Q (withTopRealPart (fun y : E ↦ ((f y : ℝ) : WithTop ℝ))) := by
    simpa using hf_conv
  simpa using
    (constrainedSubdifferentialNonemptyAtSlaterCenter
      hconv_withTop hQ_subset_interior hε hball :
      (∂[Q] (fun y : E ↦ ((f y : ℝ) : WithTop ℝ))(x)).Nonempty)

/-- Helper for Theorem 7.19: an ambient interior point of `Q` automatically has a feasible
subgradient witness for the convex objective `φ`. -/
lemma feasibleSubgradientNonempty_of_memInterior
    (Q : Set E) [FiniteDimensional ℝ E]
    {φ : E → ℝ} {x : E}
    (hφ_convex : ConvexOn ℝ Q φ)
    (hxInterior : x ∈ interior Q) :
    (∂[Q] φ(x)).Nonempty := by
  rw [mem_interior_iff_mem_nhds] at hxInterior
  rcases Metric.mem_nhds_iff.mp hxInterior with ⟨ε, hε, hballQ⟩
  -- Convert the interior ball around `x` into the existing Slater-ball nonemptiness lemma.
  exact subdifferentialWithinNonemptyOfBall Q hφ_convex hε hballQ

/-- Helper for Theorem 7.19: uniformly bounded feasible subgradients force the normal cone to be
trivial once one feasible witness exists. -/
lemma normalConeZero_of_boundedSubdifferentialWithinOfWitness
    (Q : Set E) (p : Seminorm ℝ E) [Seminorm.IsNorm p] [FiniteDimensional ℝ E]
    (φ : E → ℝ) (L : ℝ)
    {x gφ : E} (hgφ : gφ ∈ ∂[Q] φ(x))
    (hbound : ∀ ⦃g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L) :
    ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0 := by
  intro n hn
  -- Feed the explicit feasible witness into the quantitative normal-cone collapse lemma.
  exact
    eq_zero_of_mem_normalCone_of_bounded_subdifferentialWithin
      Q p φ L hgφ hn hbound

/-- Helper for Theorem 7.19: on a convex feasible set, a point with trivial normal cone is an
ambient interior point. -/
lemma mem_interior_of_trivialNormalCone
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQ_convex : Convex ℝ Q)
    {x : E} (hx : x ∈ Q)
    (hNormalZero : ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0) :
    x ∈ interior Q := by
  by_contra hx_not_interior
  have hx_not_interior_closure : x ∉ interior (closure Q) := by
    intro hx_interior_closure
    have hspan_closure_top : affineSpan ℝ (closure Q) = ⊤ := by
      -- A nonempty ambient interior forces the affine span of `closure Q` to fill the space.
      rw [← hQ_convex.closure.interior_nonempty_iff_affineSpan_eq_top]
      exact ⟨x, hx_interior_closure⟩
    have hclosure_subset_affineSpan : closure Q ⊆ affineSpan ℝ Q := by
      -- The affine span is closed in finite dimensions, so it contains the closure of `Q`.
      refine closure_minimal (subset_affineSpan ℝ Q) ?_
      exact (affineSpan ℝ Q).closed_of_finiteDimensional
    have hspan_closure_le : affineSpan ℝ (closure Q) ≤ affineSpan ℝ Q := by
      have hmono :
          affineSpan ℝ (closure Q) ≤ affineSpan ℝ ((affineSpan ℝ Q : Set E)) :=
        affineSpan_mono ℝ hclosure_subset_affineSpan
      rw [AffineSubspace.affineSpan_coe] at hmono
      exact hmono
    have hspan_top : affineSpan ℝ Q = ⊤ := by
      exact top_unique (hspan_closure_top ▸ hspan_closure_le)
    have hQ_interior_nonempty : (interior Q).Nonempty := by
      -- The same affine-span criterion then forces `Q` itself to have nonempty interior.
      rw [hQ_convex.interior_nonempty_iff_affineSpan_eq_top]
      exact hspan_top
    have hinterior_eq :
        interior (closure Q) = interior Q :=
      hQ_convex.interior_closure_eq_interior_of_nonempty_interior hQ_interior_nonempty
    exact hx_not_interior (hinterior_eq ▸ hx_interior_closure)
  have hx_frontier_closure : x ∈ frontier (closure Q) := by
    -- Once `x` is in `closure Q` but not in its interior, it is a boundary point of `closure Q`.
    rw [frontier]
    exact ⟨subset_closure (subset_closure hx), hx_not_interior_closure⟩
  rcases
      exists_supporting_hyperplane_at_boundary_point_of_closed_convex
        (closure Q) isClosed_closure hQ_convex.closure hx_frontier_closure with
    ⟨g, γ, hx_hyperplane, hsupport⟩
  have hg_normal : -g ∈ N[Q] x := by
    -- The supporting nesterovHyperplane of `closure Q` gives an outward normal, so `-g` lies in `N[Q] x`.
    rw [neg_mem_normalCone_iff]
    intro y hy
    have hy_closure : y ∈ closure Q := subset_closure hy
    have hy_le : inner ℝ g y ≤ γ := hsupport.le_offset hy_closure
    have hx_eq : inner ℝ g x = γ := by
      simpa using hx_hyperplane
    rw [inner_sub_right]
    linarith
  have hg_zero : -g = 0 := hNormalZero hg_normal
  exact hsupport.ne_zero (by simpa using hg_zero)

/-- Helper for Theorem 7.19: a local `p`-Lipschitz upper bound around `x` already forces every
whole-space subgradient at `x` to have `p`-dual norm at most the same constant. -/
lemma dualNorm_le_of_mem_subdifferential_of_local_upper_bound
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (F : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} {ε : ℝ} (hε : 0 < ε)
    (hlocal :
      ∀ ⦃z : E⦄, z ∈ Metric.ball x ε → F z ≤ F x + L * p (z - x))
    (hg : g ∈ ∂[Set.univ] F(x)) :
    p.dualNorm g ≤ L := by
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp [map_zero p], by simp⟩⟩
  · rintro r ⟨z, hz, rfl⟩
    by_cases hz_zero : z = 0
    · simp [hz_zero, hL_nonneg]
    · rcases (mem_subdifferentialWithin_iff.mp hg) with ⟨-, hsupport⟩
      let t : ℝ := ε / (2 * ‖z‖)
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_zero
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hε (mul_pos zero_lt_two hnorm_pos)
      have hxt_mem : x + t • z ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hnorm_eq : ‖x + t • z - x‖ = ε / 2 := by
          calc
            ‖x + t • z - x‖ = ‖t • z‖ := by
              abel_nf
            _ = t * ‖z‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
            _ = ε / 2 := by
              dsimp [t]
              field_simp [hnorm_pos.ne']
        rw [hnorm_eq]
        linarith
      have hsub : x + t • z - x = t • z := by
        abel_nf
      have hsupport_xt :
          F x + t * inner ℝ g z ≤ F (x + t • z) := by
        have hsupport' :
            F x + inner ℝ g ((x + t • z) - x) ≤ F (x + t • z) := by
          exact hsupport (by simp)
        simpa [hsub, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hsupport'
      have hlocal_xt :
          F (x + t • z) ≤ F x + t * (L * p z) := by
        have hlocal' := hlocal hxt_mem
        simpa [hsub, map_smul_eq_mul, Real.norm_of_nonneg ht_pos.le,
          mul_assoc, mul_left_comm, mul_comm] using hlocal'
      have hpair_le : inner ℝ g z ≤ L * p z := by
        have hscaled : t * inner ℝ g z ≤ t * (L * p z) := by
          linarith
        nlinarith [ht_pos, hscaled]
      calc
        inner ℝ g z ≤ L * p z := hpair_le
        _ ≤ L * 1 := by
          exact mul_le_mul_of_nonneg_left hz hL_nonneg
        _ = L := by ring

/-- Helper for Theorem 7.19: a local `p`-Lipschitz upper bound on a feasible ball around `x`
already forces every constrained subgradient at `x` to have `p`-dual norm at most the same
constant. -/
lemma dualNorm_le_of_mem_subdifferentialWithin_of_local_upper_bound
    [FiniteDimensional ℝ E]
    (Q : Set E)
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (F : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} {ε : ℝ} (hε : 0 < ε)
    (hballQ : Metric.ball x ε ⊆ Q)
    (hlocal :
      ∀ ⦃z : E⦄, z ∈ Metric.ball x ε → F z ≤ F x + L * p (z - x))
    (hg : g ∈ ∂[Q] F(x)) :
    p.dualNorm g ≤ L := by
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp [map_zero p], by simp⟩⟩
  · rintro r ⟨z, hz, rfl⟩
    by_cases hz_zero : z = 0
    · simp [hz_zero, hL_nonneg]
    · rcases (mem_subdifferentialWithin_iff.mp hg) with ⟨-, hsupport⟩
      let t : ℝ := ε / (2 * ‖z‖)
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_zero
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hε (mul_pos zero_lt_two hnorm_pos)
      have hxt_mem : x + t • z ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hnorm_eq : ‖x + t • z - x‖ = ε / 2 := by
          calc
            ‖x + t • z - x‖ = ‖t • z‖ := by
              abel_nf
            _ = t * ‖z‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
            _ = ε / 2 := by
              dsimp [t]
              field_simp [hnorm_pos.ne']
        rw [hnorm_eq]
        linarith
      have hxtQ : x + t • z ∈ Q := hballQ hxt_mem
      have hsub : x + t • z - x = t • z := by
        abel_nf
      have hsupport_xt :
          F x + t * inner ℝ g z ≤ F (x + t • z) := by
        -- Evaluate the constrained support inequality on the nearby feasible perturbation.
        have hsupport' :
            F x + inner ℝ g ((x + t • z) - x) ≤ F (x + t • z) := by
          exact hsupport hxtQ
        simpa [hsub, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hsupport'
      have hlocal_xt :
          F (x + t • z) ≤ F x + t * (L * p z) := by
        -- Rewrite the local upper bound along the same perturbation.
        have hlocal' := hlocal hxt_mem
        simpa [hsub, map_smul_eq_mul, Real.norm_of_nonneg ht_pos.le,
          mul_assoc, mul_left_comm, mul_comm] using hlocal'
      have hpair_le : inner ℝ g z ≤ L * p z := by
        have hscaled : t * inner ℝ g z ≤ t * (L * p z) := by
          linarith
        nlinarith [ht_pos, hscaled]
      calc
        inner ℝ g z ≤ L * p z := hpair_le
        _ ≤ L * 1 := by
          exact mul_le_mul_of_nonneg_left hz hL_nonneg
        _ = L := by ring

/-- Helper for Theorem 7.19: every ambient subgradient of the scaled seminorm branch has
`p`-dual norm at most `L`. -/
lemma dualNorm_le_of_mem_subdifferential_scaledSeminorm
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E}
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ L * p z) : E → ℝ) (x)) :
    p.dualNorm g ≤ L := by
  have hlocal :
      ∀ ⦃z : E⦄, z ∈ Metric.ball x 1 → L * p z ≤ L * p x + L * p (z - x) := by
    intro z hz
    have hp_triangle : p z ≤ p x + p (z - x) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (map_add_le_add p x (z - x))
    -- The scaled seminorm branch satisfies the required upper bound globally by the triangle
    -- inequality, so the local-upper-bound owner applies without any branch-specific geometry.
    calc
      L * p z ≤ L * (p x + p (z - x)) := by
        exact mul_le_mul_of_nonneg_left hp_triangle hL_nonneg
      _ = L * p x + L * p (z - x) := by
        ring
  -- Feed the global scaled-seminorm upper bound into the ambient dual-norm estimate.
  exact
    dualNorm_le_of_mem_subdifferential_of_local_upper_bound
      p ((fun z : E ↦ L * p z) : E → ℝ) L hL_nonneg (by norm_num) hlocal hg

/-- Helper for Theorem 7.19: once `φ` is locally controlled by the base value plus
`L * p (z - x)`, the same one-sided estimate transfers to the max objective on the non-left
branch. -/
lemma max_le_at_base_add_mul_of_nonleft_of_phi_bound
    (p : Seminorm ℝ E) (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x z : E}
    (hφz : φ z ≤ φ x + L * p (z - x))
    (hnonleft : φ x ≤ L * p x) :
    max (φ z) (L * p z) ≤ max (φ x) (L * p x) + L * p (z - x) := by
  have hx_max : max (φ x) (L * p x) = L * p x := max_eq_right hnonleft
  have hz_left :
      φ z ≤ max (φ x) (L * p x) + L * p (z - x) := by
    calc
      φ z ≤ φ x + L * p (z - x) := hφz
      _ ≤ L * p x + L * p (z - x) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hnonleft (L * p (z - x))
      _ = max (φ x) (L * p x) + L * p (z - x) := by
        rw [hx_max]
  have hp_triangle : p z ≤ p x + p (z - x) := by
    have hsum := map_add_le_add p x (z - x)
    have hrewrite : x + (z - x) = z := by
      abel_nf
    simpa [hrewrite] using hsum
  have hz_right :
      L * p z ≤ max (φ x) (L * p x) + L * p (z - x) := by
    calc
      L * p z ≤ L * (p x + p (z - x)) := by
        exact mul_le_mul_of_nonneg_left hp_triangle hL_nonneg
      _ = L * p x + L * p (z - x) := by ring
      _ = max (φ x) (L * p x) + L * p (z - x) := by
        rw [hx_max]
  -- Bound both branches separately, then recombine them through `max_le_iff`.
  exact max_le hz_left hz_right

/-- Helper for Theorem 7.19: on the non-left branch, bounded feasible subgradients of `φ`
and one explicit feasible witness at `x` force `x` into the ambient interior of `Q`. -/
lemma interior_of_boundedSubdifferentialWithin_of_witness
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    {x gφ : E} (hx : x ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L) :
    x ∈ interior Q := by
  -- Feed the explicit feasible witness into the normal-cone collapse lemma before invoking the
  -- convex-geometry interior criterion.
  have hNormalZero :
      ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0 :=
    normalConeZero_of_boundedSubdifferentialWithinOfWitness
      Q p φ L hgφ hsubgradient_bound
  exact mem_interior_of_trivialNormalCone Q hφ_convex.1 hx hNormalZero

/-- Helper for Theorem 7.19: once a feasible `φ`-subgradient is known at `x`, the bounded
constrained-subgradient hypothesis yields a local `φ z ≤ φ x + L * p (z - x)` estimate near `x`.
-/
lemma existsLocalPhiUpperBound_of_boundedSubdifferentialWithin_of_witness
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    {x gφ : E} (hx : x ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ ⦃z : E⦄, z ∈ Metric.ball x ε → φ z ≤ φ x + L * p (z - x) := by
  have hsubgradient_bound_x :
      ∀ ⦃g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L :=
    fun {g} hg ↦ hsubgradient_bound hg
  have hxInterior : x ∈ interior Q :=
    interior_of_boundedSubdifferentialWithin_of_witness
      Q p φ L hx hφ_convex hgφ hsubgradient_bound_x
  rw [mem_interior_iff_mem_nhds] at hxInterior
  rcases Metric.mem_nhds_iff.mp hxInterior with ⟨ε₀, hε₀_pos, hballQ⟩
  refine ⟨ε₀ / 2, by linarith, ?_⟩
  intro z hz
  have hzBall :
      Metric.ball z (ε₀ / 2) ⊆ Q := by
    intro w hw
    have hdist : dist w x < ε₀ := by
      calc
        dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
        _ < ε₀ / 2 + ε₀ / 2 := add_lt_add hw hz
        _ = ε₀ := by ring
    exact hballQ hdist
  rcases subdifferentialWithinNonemptyOfBall Q hφ_convex (show 0 < ε₀ / 2 by linarith) hzBall with
    ⟨gz, hgz⟩
  have hsupport_at_x : φ x ≥ φ z + inner ℝ gz (x - z) :=
    by
      exact (mem_subdifferentialWithin_iff.mp hgz).2 hx
  have hdual : p.dualNorm gz ≤ L := hsubgradient_bound hgz
  have hpair :
      inner ℝ gz (z - x) ≤ L * p (z - x) := by
    calc
      inner ℝ gz (z - x) ≤ p.dualNorm gz * p (z - x) :=
        Seminorm.inner_le_dualNorm_mul p (z - x) gz
      _ ≤ L * p (z - x) := by
        exact mul_le_mul_of_nonneg_right hdual (apply_nonneg p (z - x))
  have hsupport :
      φ z ≤ φ x + inner ℝ gz (z - x) := by
    have hrewrite : inner ℝ gz (x - z) = -inner ℝ gz (z - x) := by
      have hsub : x - z = -(z - x) := by
        abel_nf
      calc
        inner ℝ gz (x - z) = inner ℝ gz (-(z - x)) := by rw [hsub]
        _ = -inner ℝ gz (z - x) := by rw [inner_neg_right]
    rw [hrewrite] at hsupport_at_x
    linarith
  -- Compare back to `x` through the nearby constrained subgradient at `z`, then bound the
  -- resulting pairing by the dual-norm hypothesis.
  linarith

/-- Helper for Theorem 7.19: on the non-left branch, bounded feasible subgradients of `φ`
produce a local `p`-Lipschitz upper bound for the max objective around the base point once an
explicit feasible `φ`-subgradient at `x` is available. -/
lemma existsLocalMaxUpperBound_of_boundedSubdifferentialWithin_nonleft
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x gφ : E} (hx : x ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ ⦃z : E⦄, z ∈ Metric.ball x ε →
        max (φ z) (L * p z) ≤ max (φ x) (L * p x) + L * p (z - x) := by
  rcases existsLocalPhiUpperBound_of_boundedSubdifferentialWithin_of_witness
      Q p φ L hx hφ_convex hgφ hsubgradient_bound with
    ⟨ε, hε, hphi⟩
  refine ⟨ε, hε, ?_⟩
  intro z hz
  -- Transfer the local `φ` estimate to the max objective on the non-left branch at `x`.
  exact max_le_at_base_add_mul_of_nonleft_of_phi_bound p φ L hL_nonneg (hphi hz) hnonleft

/-- Helper for Theorem 7.19: on the non-left branch, a whole-space subgradient of
`z ↦ max (φ z) (L * p z)` has `p`-dual norm at most `L`. -/
lemma dualNorm_le_of_mem_subdifferential_max_nonleft_of_witness
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g gφ : E} (hx : x ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    p.dualNorm g ≤ L := by
  -- Once one feasible `φ`-subgradient is known at `x`, the bounded-subgradient hypothesis
  -- produces a local upper bound for the max objective around `x`.
  rcases existsLocalMaxUpperBound_of_boundedSubdifferentialWithin_nonleft
      Q p φ L hL_nonneg hx hφ_convex hgφ hsubgradient_bound hnonleft with
    ⟨ε, hε, hlocal⟩
  -- The generic local-upper-bound lemma then converts that local control into the dual-norm
  -- estimate for the ambient max subgradient `g`.
  exact
    dualNorm_le_of_mem_subdifferential_of_local_upper_bound
      p ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) L hL_nonneg hε hlocal hg

/-- Helper for Theorem 7.19: on the non-left branch, an ambient interior point of `Q`
already supplies the feasible `φ`-subgradient witness needed by the local-upper-bound route. -/
lemma dualNorm_le_of_mem_subdifferential_max_nonleft_of_memInterior
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} (hx : x ∈ Q) (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    p.dualNorm g ≤ L := by
  -- Interior points admit a feasible `φ`-subgradient through the existing Slater-ball helper.
  rcases feasibleSubgradientNonempty_of_memInterior Q hφ_convex hxInterior with ⟨gφ, hgφ⟩
  -- Feed that witness into the already-closed non-left local-upper-bound route.
  exact
    dualNorm_le_of_mem_subdifferential_max_nonleft_of_witness
      Q p φ L hL_nonneg hx hφ_convex hgφ hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: on the non-left branch, a feasible-set subgradient of
`z ↦ max (φ z) (L * p z)` has `p`-dual norm at most `L`. -/
lemma dualNorm_le_of_mem_subdifferential_max_nonleft
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} (hx : x ∈ Q) (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    p.dualNorm g ≤ L := by
  -- Route correction: the witness-free constrained non-left surface is false at boundary points,
  -- so this helper now records the interior hypothesis needed by the existing ambient route.
  exact
    dualNorm_le_of_mem_subdifferential_max_nonleft_of_memInterior
      Q p φ L hL_nonneg hx hxInterior hφ_convex hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: on the non-left branch, a feasible-set subgradient of
`z ↦ max (φ z) (L * p z)` gives the source-faithful strict-positivity inequality
along feasible displacements in `Q`. -/
lemma strictly_positive_expr_nonneg_of_mem_subdifferential_max_nonleft
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q) (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- Once the non-left branch gives the same dual-norm control, the generic positivity lemma
  -- closes the target expression without revisiting the branch geometry.
  have hg_dual :
      p.dualNorm g ≤ L :=
    dualNorm_le_of_mem_subdifferential_max_nonleft
      Q p φ L hL_nonneg hx hxInterior hφ_convex hsubgradient_bound hnonleft hg
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: on the non-left branch, one explicit feasible `φ`-subgradient
witness is enough to finish the ambient strict-positivity inequality. -/
lemma strictly_positive_expr_nonneg_of_nonleft_of_witness
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g gφ : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- First convert the explicit feasible witness into the dual-norm control for the ambient
  -- max-subgradient.
  have hg_dual :
      p.dualNorm g ≤ L :=
    dualNorm_le_of_mem_subdifferential_max_nonleft_of_witness
      Q p φ L hL_nonneg hx hφ_convex hgφ hsubgradient_bound hnonleft hg
  -- Then reuse the generic positivity inequality once the dual-norm bound is available.
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: on the strict-right branch, ambient interior of `Q` is the only
remaining structural input needed by the already-closed non-left positivity route. -/
lemma strictly_positive_expr_nonneg_of_strictRight_of_memInterior
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hstrictRight : φ x < L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- Rewrite the strict-right branch as the non-left branch, now that an interior certificate is
  -- provided explicitly.
  exact
    strictly_positive_expr_nonneg_of_mem_subdifferential_max_nonleft
      Q p φ L hL_nonneg hx hy hxInterior hφ_convex hsubgradient_bound
      (le_of_lt hstrictRight) hg

/-- Helper for Theorem 7.19: a feasible-set subgradient of the max objective satisfies the
source-faithful strict-positivity inequality on `Q` when it comes from the ambient owner and the
left branch is strictly active. -/
lemma strictly_positive_expr_nonneg_of_mem_subdifferential_max_strictLeft
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x))
    (hstrictLeft : L * p x < φ x) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  have hQ_convex : Convex ℝ Q := hφ_convex.1
  have hp_convex : ConvexOn ℝ Q (fun z : E ↦ L * p z) :=
    convexOn_scaledSeminorm Q p L hQ_convex hL_nonneg
  have hgQ :
      g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) :=
    mem_subdifferentialWithin_of_mem_subdifferential Q hx hg
  -- Restrict the ambient max-subgradient to `Q`, then isolate the active left branch.
  have hgφ :
      g ∈ ∂[Q] φ(x) :=
    mem_subdifferentialWithin_left_of_mem_max_strictLeft
      Q hQ_convex hφ_convex hp_convex hgQ hstrictLeft
  have hg_dual : p.dualNorm g ≤ L := hsubgradient_bound hgφ
  -- The generic dual-norm positivity lemma finishes the strict-left branch.
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: on the strict-right branch, the constrained-to-ambient remainder
decomposition compares the ambient max-subgradient pairing with the ambient scaled-seminorm
pairing in the reverse direction. This records the exact sign obstruction left by the Chapter 3
remainder API. -/
lemma strictRightRemainder_pairing_le_scaledSeminormPairing
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hstrictRight : φ x < L * p x)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    ∃ gψ : E,
      gψ ∈ ∂ (fun z : E ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ))(x) ∧
        inner ℝ g (y - x) ≤ inner ℝ gψ (y - x) := by
  have hQ_convex : Convex ℝ Q := hφ_convex.1
  have hgQ :
      g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) :=
    mem_subdifferentialWithin_of_mem_subdifferential Q hx hg
  rcases
      exists_scaledSeminormSubgradient_of_strictRight
        Q p φ L hL_nonneg hx hQ_convex hφ_convex hstrictRight hgQ with
    ⟨gψ, hgψ, hnormal⟩
  refine ⟨gψ, hgψ, ?_⟩
  -- The normal-cone remainder makes the ambient max-subgradient pairing no larger than the
  -- ambient scaled-seminorm pairing on feasible displacements.
  exact inner_le_of_sub_mem_normalCone Q hy hnormal

/-- Helper for Theorem 7.19: a constrained subgradient of the max objective is exactly an ambient
subgradient of the corresponding `⊤`-extension. -/
lemma mem_subdifferential_topExtension_max_of_mem_subdifferentialWithin
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    {x g : E}
    (hg : g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    g ∈ ∂ (fun z : E ↦ if z ∈ Q then (((max (φ z) (L * p z)) : ℝ) : WithTop ℝ) else ⊤) (x) := by
  classical
  -- Rewrite the constrained owner as the ambient owner of the canonical `⊤`-extension.
  rw [subdifferential_topExtension_eq_constrainedSubdifferential]
  simpa using hg

/-- Helper for Theorem 7.19: one explicit feasible `φ`-subgradient witness is enough to recover
the ambient strict-positivity inequality for the augmented objective on `Q`. -/
lemma strictPositivityExpr_nonneg_of_mem_maxSubdifferential
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g gφ : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L)
    (hg : g ∈ ∂[Set.univ] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- Route correction: the witness-free non-left branch is false on boundary points, so the
  -- repaired helper now splits by branch after fixing an explicit feasible `φ`-subgradient.
  by_cases hstrictLeft : L * p x < φ x
  · -- On the strict-left branch, the ambient max-subgradient already restricts to `φ`.
    exact
      strictly_positive_expr_nonneg_of_mem_subdifferential_max_strictLeft
        Q p φ L hL_nonneg hx hy hφ_convex hsubgradient_bound hg hstrictLeft
  · have hnonleft : φ x ≤ L * p x := by linarith
    -- On the non-left branch, the explicit feasible witness feeds the existing closure lemma.
    exact
      strictly_positive_expr_nonneg_of_nonleft_of_witness
        Q p φ L hL_nonneg hx hy hφ_convex hgφ hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: the two-branch max is the `Fin 2` pointwise supremum used by the
Chapter 3 active-index API. -/
lemma max_eq_pointwiseSupremumOn_finTwo
    {f ψ : E → ℝ} {x : E} :
    pointwiseSupremumOn (Set.univ : Set (Fin 2))
      (fun z i ↦ ((![f z, ψ z] : Fin 2 → ℝ) i : WithTop ℝ)) x =
        (max (f x) (ψ x) : WithTop ℝ) := by
  -- Compare the supremum with the two explicit branch values in both directions.
  let s : Set (WithTop ℝ) :=
    (fun y : Fin 2 ↦ (((![f x, ψ x] : Fin 2 → ℝ) y : ℝ) : WithTop ℝ)) '' (Set.univ : Set (Fin 2))
  have hs_nonempty : s.Nonempty := by
    refine ⟨(f x : WithTop ℝ), ?_⟩
    exact ⟨0, by simp, by simp⟩
  have hs_upper : BddAbove s := ⟨⊤, by intro r hr; exact le_top⟩
  change sSup s = (max (f x) (ψ x) : WithTop ℝ)
  refine le_antisymm ?_ ?_
  · refine csSup_le hs_nonempty ?_
    rintro r ⟨i, -, rfl⟩
    fin_cases i <;> simp
  · refine (max_le_iff.mpr ?_)
    constructor
    · exact le_csSup hs_upper ⟨0, by simp, by simp⟩
    · exact le_csSup hs_upper ⟨1, by simp, by simp⟩

/-- Helper for Theorem 7.19: for real-valued branches, the effective domain of the normalized
two-index supremum is exactly the ambient feasible set `Q`. -/
lemma mem_pointwiseSupremumOnEffectiveDomain_finTwo_iff
    {Q : Set E} {f ψ : E → ℝ} {x : E} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q (Set.univ : Set (Fin 2))
        (fun z i ↦ ((![f z, ψ z] : Fin 2 → ℝ) i : WithTop ℝ)) ↔
      x ∈ Q := by
  rw [mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top]
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    rw [max_eq_pointwiseSupremumOn_finTwo]
    simp

/-- Helper for Theorem 7.19: if the left branch is strictly larger at `x`, then the normalized
active-index set collapses to the singleton `{0}`. -/
lemma activePointwiseSupremumOnIndices_finTwo_of_left_lt
    {f ψ : E → ℝ} {x : E} (h : ψ x < f x) :
    activePointwiseSupremumOnIndices (Set.univ : Set (Fin 2))
      (fun z i ↦ ((![f z, ψ z] : Fin 2 → ℝ) i : WithTop ℝ)) x = {0} := by
  -- Reduce the active-index predicate to the two concrete coordinates and simplify the max.
  ext i
  fin_cases i
  · rw [mem_activePointwiseSupremumOnIndices_univ_iff, max_eq_pointwiseSupremumOn_finTwo]
    simpa [max_eq_left (le_of_lt h)] using le_of_lt h
  · rw [mem_activePointwiseSupremumOnIndices_univ_iff, max_eq_pointwiseSupremumOn_finTwo]
    simpa [max_eq_left (le_of_lt h)] using h

/-- Helper for Theorem 7.19: if the right branch is strictly larger at `x`, then the normalized
active-index set collapses to the singleton `{1}`. -/
lemma activePointwiseSupremumOnIndices_finTwo_of_right_lt
    {f ψ : E → ℝ} {x : E} (h : f x < ψ x) :
    activePointwiseSupremumOnIndices (Set.univ : Set (Fin 2))
      (fun z i ↦ ((![f z, ψ z] : Fin 2 → ℝ) i : WithTop ℝ)) x = {1} := by
  -- Reduce the active-index predicate to the two concrete coordinates and simplify the max.
  ext i
  fin_cases i
  · rw [mem_activePointwiseSupremumOnIndices_univ_iff, max_eq_pointwiseSupremumOn_finTwo]
    simpa [max_eq_right (le_of_lt h)] using h
  · rw [mem_activePointwiseSupremumOnIndices_univ_iff, max_eq_pointwiseSupremumOn_finTwo]
    simpa [max_eq_right (le_of_lt h)] using le_of_lt h

/-- Helper for Theorem 7.19: at a tie point, both normalized branches are active, so the active
index set is all of `Fin 2`. -/
lemma activePointwiseSupremumOnIndices_finTwo_of_eq
    {f ψ : E → ℝ} {x : E} (h : f x = ψ x) :
    activePointwiseSupremumOnIndices (Set.univ : Set (Fin 2))
      (fun z i ↦ ((![f z, ψ z] : Fin 2 → ℝ) i : WithTop ℝ)) x = Set.univ := by
  -- With equal branch values, each of the two coordinates attains the same maximum.
  ext i
  fin_cases i <;>
    rw [mem_activePointwiseSupremumOnIndices_univ_iff, max_eq_pointwiseSupremumOn_finTwo] <;>
    simp [h]

namespace TopExtensionNonleft

/-- Helper for Theorem 7.19: a top-extension max-subgradient is the same as a constrained
subgradient of the underlying real-valued max objective on `Q`. -/
lemma mem_subdifferentialWithin_max_of_mem_topExtensionSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    {x g : E} (hx : x ∈ Q)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) := by
  -- Rewrite the `⊤`-extension owner into the canonical constrained owner used by the branch API.
  have htopEq :
      topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)) =
        fun z : E ↦ if z ∈ Q then ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)) else ⊤ := by
    funext z
    by_cases hz : z ∈ Q <;> simp [topExtensionOn, hz]
  have hgExt :
      g ∈ ∂ (fun z : E ↦
        if z ∈ Q then ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)) else ⊤) (x) := by
    rw [← htopEq]
    exact hg
  simpa using
    mem_subdifferential_topExtension_iff_mem_constrainedSubdifferential.mp hgExt

/-- Helper for Theorem 7.19: on the non-left branch, one explicit feasible `φ`-subgradient
witness is enough to recover the top-extension strict-positivity inequality on the constrained
owner surface. -/
lemma nonneg_of_witness
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g gφ : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hgφ : gφ ∈ ∂[Q] φ(x))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄,
        x ∈ Q →
        g ∈ ∂[Q] φ(x) →
        p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  have hboundAtX :
      ∀ ⦃g' : E⦄, g' ∈ ∂[Q] φ(x) → p.dualNorm g' ≤ L :=
    fun {g'} hg' ↦ hsubgradient_bound hx hg'
  have hboundOnQ :
      ∀ ⦃z g' : E⦄, g' ∈ ∂[Q] φ(z) → p.dualNorm g' ≤ L :=
    fun {z} {g'} hg' ↦
      hsubgradient_bound ((mem_subdifferentialWithin_iff.mp hg').1) hg'
  have hxInterior : x ∈ interior Q :=
    interior_of_boundedSubdifferentialWithin_of_witness
      Q p φ L hx hφ_convex hgφ hboundAtX
  rcases Metric.mem_nhds_iff.mp ((mem_interior_iff_mem_nhds).mp hxInterior) with
    ⟨εQ, hεQ, hballQ⟩
  rcases existsLocalMaxUpperBound_of_boundedSubdifferentialWithin_nonleft
      Q p φ L hL_nonneg hx hφ_convex hgφ hboundOnQ hnonleft with
    ⟨εF, hεF, hlocalF⟩
  let ε : ℝ := min εQ εF
  have hε : 0 < ε := by
    exact lt_min hεQ hεF
  have hballQ' : Metric.ball x ε ⊆ Q := by
    intro z hz
    exact hballQ (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hlocal :
      ∀ ⦃z : E⦄, z ∈ Metric.ball x ε →
        max (φ z) (L * p z) ≤ max (φ x) (L * p x) + L * p (z - x) := by
    intro z hz
    exact hlocalF (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hgQ :
      g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) := by
    -- Repackage the top-extension subgradient through the canonical owner bridge.
    have htopEq :
        topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)) =
          fun z : E ↦ if z ∈ Q then ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)) else ⊤ := by
      funext z
      by_cases hz : z ∈ Q <;> simp [topExtensionOn, hz]
    have hgExt :
        g ∈ ∂ (fun z : E ↦
          if z ∈ Q then ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)) else ⊤) (x) := by
      rw [← htopEq]
      exact hg
    have hbridge :
        g ∈ ∂ (fun z : E ↦
          if z ∈ Q then ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)) else ⊤) (x) ↔
          g ∈ ∂[Q] (fun z : E ↦ ((((max (φ z) (L * p z)) : ℝ) : WithTop ℝ)))(x) :=
      mem_subdifferential_topExtension_iff_mem_constrainedSubdifferential
    simpa using hbridge.mp hgExt
  have hg_dual : p.dualNorm g ≤ L :=
    dualNorm_le_of_mem_subdifferentialWithin_of_local_upper_bound
      Q p ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) L hL_nonneg hε hballQ' hlocal hgQ
  -- The generic dual-norm positivity inequality now closes the constrained top-extension branch.
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: ambient interior of `Q` immediately supplies the feasible
`φ`-subgradient witness needed by the non-left top-extension route. -/
lemma nonneg_of_memInterior
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g : E⦄,
        z ∈ Q →
        g ∈ ∂[Q] φ(z) →
        p.dualNorm g ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- An ambient interior certificate turns into an explicit feasible `φ`-subgradient witness.
  rcases feasibleSubgradientNonempty_of_memInterior Q hφ_convex hxInterior with ⟨gφ, hgφ⟩
  -- Feed that witness into the already-closed top-extension non-left lemma.
  exact
    nonneg_of_witness
      Q p φ L hL_nonneg hx hy hφ_convex hgφ hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: the theorem-faithful non-left branch already closes once either
`x` is interior to `Q` or `φ` has one feasible constrained subgradient at `x`. -/
lemma nonneg_of_memInterior_or_feasibleSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x))
    (hcase : x ∈ interior Q ∨ (∂[Q] φ(x)).Nonempty) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  rcases hcase with hxInterior | hφ_nonempty
  · -- The interior branch is already handled by the dedicated top-extension non-left lemma.
    exact
      nonneg_of_memInterior
        Q p φ L hL_nonneg hx hy hxInterior hφ_convex hsubgradient_bound hnonleft hg
  · rcases hφ_nonempty with ⟨gφ, hgφ⟩
    -- One feasible `φ`-subgradient witness closes the same non-left branch directly.
    exact
      nonneg_of_witness
        Q p φ L hL_nonneg hx hy hφ_convex hgφ hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: if the feasible `φ`-subdifferential at `x` is empty, then `x`
cannot lie in the ambient interior of `Q`. -/
lemma not_memInterior_of_feasibleSubgradientEmpty
    (Q : Set E) [FiniteDimensional ℝ E]
    {φ : E → ℝ} {x : E}
    (hφ_convex : ConvexOn ℝ Q φ)
    (hφ_empty : ¬ (∂[Q] φ(x)).Nonempty) :
    x ∉ interior Q := by
  intro hxInterior
  -- Interior points admit a feasible `φ`-subgradient through the Slater-ball helper.
  exact hφ_empty (feasibleSubgradientNonempty_of_memInterior Q hφ_convex hxInterior)

/-- Helper for Theorem 7.19: once the current non-left base point is already interior, the
top-extension non-left core closes immediately through the existing interior route. -/
lemma nonneg_of_topExtensionNonleftCore_of_memInterior
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hxInterior : x ∈ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- The ambient interior certificate already supplies the feasible `φ`-subgradient witness
  -- consumed by the existing non-left top-extension closer.
  exact
    nonneg_of_memInterior
      Q p φ L hL_nonneg hx hy hxInterior hφ_convex hsubgradient_bound hnonleft hg

/-- Helper for Theorem 7.19: on the strict-right branch, the repaired theorem-level
everywhere-feasible-subgradient hypothesis supplies the witness needed at the current base point
`x`. -/
lemma feasibleSubgradient_of_topExtensionStrictRight
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E}
    (hx : x ∈ Q)
    (hx_notInterior : x ∉ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (hsubgradient_nonempty :
      ∀ ⦃z : E⦄, z ∈ Q → (∂[Q] φ(z)).Nonempty)
    (hgQ : g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x))
    (hstrictRight : φ x < L * p x) :
    (∂[Q] φ(x)).Nonempty := by
  let _ := p
  let _ := L
  let _ := hL_nonneg
  let _ := hx_notInterior
  let _ := hφ_convex
  let _ := hsubgradient_bound
  let _ := hgQ
  let _ := hstrictRight
  exact hsubgradient_nonempty hx

/-- Helper for Theorem 7.19: on the tie branch, the repaired theorem-level
everywhere-feasible-subgradient hypothesis supplies the witness needed at the current base point
`x`. -/
lemma feasibleSubgradient_of_topExtensionTie
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E}
    (hx : x ∈ Q)
    (hx_notInterior : x ∉ interior Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (hsubgradient_nonempty :
      ∀ ⦃z : E⦄, z ∈ Q → (∂[Q] φ(z)).Nonempty)
    (hgQ : g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x))
    (htie : φ x = L * p x) :
    (∂[Q] φ(x)).Nonempty := by
  let _ := p
  let _ := L
  let _ := hL_nonneg
  let _ := hx_notInterior
  let _ := hφ_convex
  let _ := hsubgradient_bound
  let _ := hgQ
  let _ := htie
  exact hsubgradient_nonempty hx

/-- Helper for Theorem 7.19: the ambient top-extension bound on `φ` transfers directly to the
constrained subdifferential surface on `Q`. -/
lemma dualNorm_le_of_mem_constrainedSubdifferential_of_topExtensionBound
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    {x g : E}
    (hx : x ∈ Q)
    (hboundAtX :
      ∀ ⦃g' : E⦄,
        g' ∈ ∂ (topExtensionOn Q φ)(x) →
        p.dualNorm g' ≤ L)
    (hg : g ∈ ∂[Q] φ(x)) :
    p.dualNorm g ≤ L := by
  -- Rewrite the constrained owner as the canonical `⊤`-extension owner, then apply the ambient
  -- theorem hypothesis at the same feasible base point `x`.
  have htopEq :
      topExtensionOn Q φ =
        fun z : E ↦ if z ∈ Q then (((φ z : ℝ) : WithTop ℝ)) else ⊤ := by
    funext z
    by_cases hz : z ∈ Q <;> simp [topExtensionOn, hz]
  have hbridge :
      g ∈ ∂ (fun z : E ↦ if z ∈ Q then (((φ z : ℝ) : WithTop ℝ)) else ⊤) (x) ↔
        g ∈ ∂[Q] (fun z : E ↦ (((φ z : ℝ) : WithTop ℝ)))(x) :=
    mem_subdifferential_topExtension_iff_mem_constrainedSubdifferential
  have hgTop :
      g ∈ ∂ (topExtensionOn Q φ)(x) := by
    rw [htopEq]
    exact hbridge.mpr (by simpa using hg)
  exact hboundAtX hgTop

/-- Helper for Theorem 7.19: once the bounded-`φ` hypothesis has been transported to the
constrained owner, the only remaining non-left blocker is the actual top-extension max
subgradient `hg` together with the strict-right/tie geometry at `x`. -/
lemma nonneg_of_topExtensionNonleftCore
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (hsubgradient_nonempty :
      ∀ ⦃z : E⦄, z ∈ Q → (∂[Q] φ(z)).Nonempty)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- Route correction: the old witness-free dichotomy forgot the actual max-subgradient owner
  -- data. The remaining blocker must stay attached to this concrete `hg`.
  by_cases hxInterior : x ∈ interior Q
  · -- The interior case is already solved by the dedicated top-extension non-left interior route.
    exact
      nonneg_of_topExtensionNonleftCore_of_memInterior
        Q p φ L hL_nonneg hx hy hxInterior hφ_convex hsubgradient_bound hnonleft hg
  · by_cases hφ_nonempty : (∂[Q] φ(x)).Nonempty
    · rcases hφ_nonempty with ⟨gφ, hgφ⟩
      -- One feasible `φ`-subgradient witness closes the whole non-left branch through the
      -- existing top-extension witness lemma.
      exact
        nonneg_of_witness
          Q p φ L hL_nonneg hx hy hφ_convex hgφ hsubgradient_bound hnonleft hg
    · have hgQ :
          g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) :=
        mem_subdifferentialWithin_max_of_mem_topExtensionSubgradient Q p φ L hx hg
      -- Route correction: after dispatching the easy interior and witness cases, the only
      -- remaining frontier is the genuine boundary/no-witness branch on the current owner `hg`.
      by_cases hstrictRight : φ x < L * p x
      · have hφ_nonempty' :
            (∂[Q] φ(x)).Nonempty :=
          feasibleSubgradient_of_topExtensionStrictRight
            Q p φ L hL_nonneg hx hxInterior hφ_convex hsubgradient_bound
            hsubgradient_nonempty hgQ hstrictRight
        exact False.elim (hφ_nonempty hφ_nonempty')
      · have htie : φ x = L * p x := le_antisymm hnonleft (le_of_not_gt hstrictRight)
        have hφ_nonempty' :
            (∂[Q] φ(x)).Nonempty :=
          feasibleSubgradient_of_topExtensionTie
            Q p φ L hL_nonneg hx hxInterior hφ_convex hsubgradient_bound
            hsubgradient_nonempty hgQ htie
        exact False.elim (hφ_nonempty hφ_nonempty')

/-- Helper for Theorem 7.19: on the strict-right branch, if the normal cone at `x` is already
trivial, then the constrained max-subgradient is really a scaled-seminorm subgradient, so the
generic dual-norm positivity inequality closes the branch. -/
lemma nonneg_of_topExtensionStrictRight_of_trivialNormalCone
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hstrictRight : φ x < L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x))
    (hNormalZero : ∀ ⦃n : E⦄, n ∈ N[Q] x → n = 0) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  have hQ_convex : Convex ℝ Q := hφ_convex.1
  have hp_convex : ConvexOn ℝ Q (fun z : E ↦ L * p z) :=
    convexOn_scaledSeminorm Q p L hQ_convex hL_nonneg
  have hgQ :
      g ∈ ∂[Q] ((fun z : E ↦ max (φ z) (L * p z)) : E → ℝ) (x) :=
    mem_subdifferentialWithin_max_of_mem_topExtensionSubgradient Q p φ L hx hg
  -- Restrict the max-subgradient to the active right branch before collapsing the normal cone.
  have hgScaled :
      g ∈ ∂[Q] ((fun z : E ↦ L * p z) : E → ℝ)(x) :=
    mem_subdifferentialWithin_right_of_mem_max_strictRight
      Q hQ_convex hφ_convex hp_convex hgQ hstrictRight
  have hg_dual : p.dualNorm g ≤ L :=
    dualNorm_le_of_mem_subdifferentialWithin_scaledSeminorm
      Q p L hQ_convex hL_nonneg hgScaled hNormalZero
  -- Once the current owner subgradient has the expected dual bound, the generic positivity
  -- inequality finishes the strict-right branch.
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: on the tie branch, direct dual control of the current owner
subgradient `g` already closes the target inequality. -/
lemma nonneg_of_topExtensionTie_of_dualNormLe
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (htie : φ x = L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x))
    (hg_dual : p.dualNorm g ≤ L) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  -- On the tie branch, once the current owner subgradient already has the expected dual bound,
  -- the branch geometry is no longer needed and the generic positivity inequality closes.
  exact strictly_positive_expr_nonneg_of_dualNorm_le p φ L hg_dual

/-- Helper for Theorem 7.19: on the tie branch, one feasible `φ`-subgradient witness is enough
to reuse the existing top-extension non-left witness route. -/
lemma nonneg_of_topExtensionTie_of_feasibleSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (htie : φ x = L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x))
    (hφ_nonempty : (∂[Q] φ(x)).Nonempty) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  rcases hφ_nonempty with ⟨gφ, hgφ⟩
  -- The tie identity turns the witness branch into the already-closed non-left witness lemma.
  exact
    nonneg_of_witness
      Q p φ L hL_nonneg hx hy hφ_convex hgφ hsubgradient_bound
      (by simpa [htie] using htie.le) hg

/-- Helper for Theorem 7.19: once the tie branch yields either direct dual control of `g` or a
feasible `φ`-subgradient witness, the target non-left inequality follows immediately. -/
lemma nonneg_of_topExtensionTie_of_dualNormLe_or_feasibleSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L)
    (htie : φ x = L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x))
    (hcase : p.dualNorm g ≤ L ∨ (∂[Q] φ(x)).Nonempty) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  rcases hcase with hg_dual | hφ_nonempty
  · -- Dispatch the direct dual-bound branch to the dedicated tie closer.
    exact
      nonneg_of_topExtensionTie_of_dualNormLe
        Q p φ L hL_nonneg hx hy hφ_convex htie hg hg_dual
  · -- Dispatch the witness branch to the dedicated tie witness closer.
    exact
      nonneg_of_topExtensionTie_of_feasibleSubgradient
        Q p φ L hL_nonneg hx hy hφ_convex hsubgradient_bound htie hg hφ_nonempty

/-- Helper for Theorem 7.19: the non-left top-extension branch now reduces directly to the
actual max-subgradient `hg` on the transported constrained-owner surface. -/
lemma nonneg_of_topExtensionBound
    (Q : Set E) [FiniteDimensional ℝ E]
    [DecidablePred fun z : E ↦ z ∈ Q]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q φ)
    (hsubgradient_bound :
      ∀ ⦃z g : E⦄,
        z ∈ Q →
        g ∈ ∂ (topExtensionOn Q φ)(z) →
        p.dualNorm g ≤ L)
    (hsubgradient_nonempty :
      ∀ ⦃z : E⦄, z ∈ Q → (∂[Q] φ(z)).Nonempty)
    (hnonleft : φ x ≤ L * p x)
    (hg : g ∈ ∂ (topExtensionOn Q (fun z : E ↦ max (φ z) (L * p z)))(x)) :
    0 ≤ max (φ y) (L * p y) + max (φ x) (L * p x) + inner ℝ g (y - x) := by
  have hboundWithin :
      ∀ ⦃z g' : E⦄,
        z ∈ Q →
        g' ∈ ∂[Q] φ(z) →
        p.dualNorm g' ≤ L := by
    intro z g' hz hg'
    -- Transport the global ambient hypothesis pointwise to the constrained owner.
    exact
      dualNorm_le_of_mem_constrainedSubdifferential_of_topExtensionBound
        Q p φ L hz (fun {u} hu ↦ hsubgradient_bound hz hu) hg'
  -- Route correction: the old global interior/witness helper was too weakly attached to the real
  -- owner data. The remaining non-left proof must work directly with this `hg`.
  exact
    nonneg_of_topExtensionNonleftCore
      Q p φ L hL_nonneg hx hy hφ_convex hboundWithin hsubgradient_nonempty hnonleft hg

end TopExtensionNonleft

/-- The zero extension of a source-side real-valued function `φ : Q → ℝ` to the ambient space. -/
noncomputable def zeroExtensionOn (Q : Set E) (φ : Q → ℝ) : E → ℝ := by
  classical
  exact fun x : E ↦ if hx : x ∈ Q then φ ⟨x, hx⟩ else 0

@[simp] theorem zeroExtensionOn_apply_of_mem
    {Q : Set E} {φ : Q → ℝ} {x : E} (hx : x ∈ Q) :
    zeroExtensionOn Q φ x = φ ⟨x, hx⟩ := by
  classical
  simp [zeroExtensionOn, hx]

@[simp] theorem zeroExtensionOn_apply_of_not_mem
    {Q : Set E} {φ : Q → ℝ} {x : E} (hx : x ∉ Q) :
    zeroExtensionOn Q φ x = 0 := by
  classical
  simp [zeroExtensionOn, hx]

/-- The source augmented objective from Theorem 7.19, viewed as a function on the feasible set
`Q`. -/
def augmentedFunctionOn {Q : Set E} (p : Seminorm ℝ E) (φ : Q → ℝ) (L : ℝ) : Q → ℝ :=
  fun x : Q ↦ max (φ x) (L * p x)

@[simp] theorem augmentedFunctionOn_apply
    {Q : Set E} {p : Seminorm ℝ E} {φ : Q → ℝ} {L : ℝ} (x : Q) :
    augmentedFunctionOn p φ L x = max (φ x) (L * p x) := rfl

/-- The canonical ambient representative of the source augmented objective from Theorem 7.19,
obtained by combining the zero extension of `φ` with the seminorm branch on the whole space. -/
def augmentedZeroExtensionOn (Q : Set E) (p : Seminorm ℝ E) (φ : Q → ℝ) (L : ℝ) : E → ℝ :=
  fun x : E ↦ max (zeroExtensionOn Q φ x) (L * p x)

@[simp] theorem augmentedZeroExtensionOn_apply_of_mem
    {Q : Set E} {p : Seminorm ℝ E} {φ : Q → ℝ} {L : ℝ} {x : E} (hx : x ∈ Q) :
    augmentedZeroExtensionOn Q p φ L x = augmentedFunctionOn p φ L ⟨x, hx⟩ := by
  simp [augmentedZeroExtensionOn, augmentedFunctionOn, zeroExtensionOn, hx]

/-- Helper for Theorem 7.19: an ambient subgradient of the zero extension already gives a
feasible constrained subgradient witness on `Q`. -/
lemma feasibleSubgradientNonempty_of_mem_subdifferential_zeroExtensionOn
    (Q : Set E) [FiniteDimensional ℝ E]
    {φ : Q → ℝ} {x g : E}
    (hx : x ∈ Q)
    (hg : g ∈ ∂[Set.univ] (zeroExtensionOn Q φ)(x)) :
    (∂[Q] (zeroExtensionOn Q φ)(x)).Nonempty := by
  -- Restrict the ambient owner directly to the feasible owner at the same base point.
  exact ⟨g, mem_subdifferentialWithin_of_mem_subdifferential Q hx hg⟩

/-- Helper for Theorem 7.19: a feasible-point subgradient of the ambient augmented zero
extension is also a subgradient of the corresponding `⊤`-extension. -/
lemma mem_subdifferential_topExtension_augmentedZeroExtensionOn_of_mem_subdifferential
    (Q : Set E)
    (p : Seminorm ℝ E) (φ : Q → ℝ) (L : ℝ)
    {x g : E} (hx : x ∈ Q)
    (hg : g ∈ ∂[Set.univ] (augmentedZeroExtensionOn Q p φ L)(x)) :
    g ∈ ∂ (topExtensionOn Q (augmentedZeroExtensionOn Q p φ L))(x) := by
  rw [mem_subdifferentialWithin_iff] at hg
  rw [mem_subdifferential_iff]
  refine ⟨?_, ?_⟩
  · -- The top extension is finite at every feasible base point.
    simpa [topExtensionOn, hx]
  · intro y hy
    by_cases hyQ : y ∈ Q
    · -- On feasible points, the `⊤`-extension agrees with the ambient augmented zero extension.
      have hsupport := hg.2 (by simpa using hyQ)
      simpa [topExtensionOn, hx, hyQ, WithTop.coe_add] using hsupport
    · -- Off `Q`, the `⊤`-extension inequality is automatic.
      simpa [topExtensionOn, hyQ] using hy

/-- Helper for Theorem 7.19: the bounded constrained-subgradient hypothesis on
`zeroExtensionOn Q φ` transports to the corresponding `⊤`-extension owner at the same feasible
base point. -/
lemma dualNormLe_of_mem_topExtension_zeroExtensionOn_subdifferential
    (Q : Set E)
    (p : Seminorm ℝ E) (φ : Q → ℝ) (L : ℝ)
    {x g : E} (hx : x ∈ Q)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) → p.dualNorm g ≤ L)
    (hg : g ∈ ∂ (topExtensionOn Q (zeroExtensionOn Q φ))(x)) :
    p.dualNorm g ≤ L := by
  rw [mem_subdifferential_iff] at hg
  have hgQ : g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) := by
    rw [mem_subdifferentialWithin_iff]
    refine ⟨hx, ?_⟩
    intro y hy
    have hyTop : y ∈ dom (topExtensionOn Q (zeroExtensionOn Q φ)) := by
      simpa [topExtensionOn, hy]
    -- Restrict the top-extension support inequality back to the feasible owner.
    have hsupport := hg.2 hyTop
      simpa [topExtensionOn, hx, hy, WithTop.coe_add] using hsupport
  exact hsubgradient_bound hgQ

/-- Helper for Theorem 7.19: on the non-left branch, a constrained scaled-seminorm subgradient on
`Q` upgrades to the ambient scaled-seminorm owner once the original ambient max-subgradient still
controls the off-`Q` side. -/
lemma mem_subdifferential_scaledSeminorm_of_mem_subdifferentialWithin_scaledSeminorm_of_mem_augmentedZeroExtensionOn_subdifferential_nonleft
    (Q : Set E)
    (p : Seminorm ℝ E) (φ : Q → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E} (hx : x ∈ Q)
    (hnonleft : zeroExtensionOn Q φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] (augmentedZeroExtensionOn Q p φ L)(x))
    (hgScaledQ : g ∈ ∂[Q] ((fun z : E ↦ L * p z) : E → ℝ)(x)) :
    g ∈ ∂ (fun z : E ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ))(x) := by
  rw [mem_subdifferentialWithin_iff] at hg hgScaledQ
  rw [mem_subdifferential_coe_real_iff]
  intro y
  by_cases hyQ : y ∈ Q
  · -- On feasible points, the constrained scaled-branch support inequality is already exact.
    exact hgScaledQ.2 hyQ
  · have hsupport := hg.2 (by simp)
    -- Off `Q`, the original ambient max owner coincides with the scaled-seminorm branch.
    simpa [augmentedZeroExtensionOn, hx, hyQ, max_eq_right hnonleft,
      max_eq_right (mul_nonneg hL_nonneg (apply_nonneg p y))] using hsupport

/-- Helper for Theorem 7.19: after removing the interior and witness cases, the only remaining
frontier is the boundary/no-witness non-left branch for the actual ambient owner
`augmentedZeroExtensionOn Q p φ L`. -/
lemma dualNormLe_of_mem_augmentedZeroExtensionOn_subdifferential_nonleft_of_noFeasibleSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : Q → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x g : E}
    (hx : x ∈ Q)
    (hφ_convex : ConvexOn ℝ Q (zeroExtensionOn Q φ))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) → p.dualNorm g ≤ L)
    (hnonleft : zeroExtensionOn Q φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] (augmentedZeroExtensionOn Q p φ L)(x))
    (hφ_empty : ¬ (∂[Q] (zeroExtensionOn Q φ)(x)).Nonempty) :
    p.dualNorm g ≤ L := by
  have hx_notInterior : x ∉ interior Q := by
    intro hxInterior
    exact hφ_empty (feasibleSubgradientNonempty_of_memInterior Q hφ_convex hxInterior)
  have hgQ :
      g ∈ ∂[Q] (augmentedZeroExtensionOn Q p φ L)(x) :=
    mem_subdifferentialWithin_of_mem_subdifferential Q hx hg
  let _ := hL_nonneg
  let _ := hsubgradient_bound
  let _ := hnonleft
  let _ := hgQ
  let _ := hx_notInterior
  have hgTop :
      g ∈ ∂ (topExtensionOn Q (augmentedZeroExtensionOn Q p φ L))(x) :=
    mem_subdifferential_topExtension_augmentedZeroExtensionOn_of_mem_subdifferential
      Q p φ L hx hg
  have hgTopMax :
      g ∈ ∂ (topExtensionOn Q
        (fun z : E ↦ max (zeroExtensionOn Q φ z) (L * p z)))(x) := by
    -- Normalize the top-extension owner to the explicit max surface used by the older branch API.
    simpa [augmentedZeroExtensionOn] using hgTop
  have hzeroTopBound :
      ∀ ⦃g' : E⦄, g' ∈ ∂ (topExtensionOn Q (zeroExtensionOn Q φ))(x) → p.dualNorm g' ≤ L := by
    intro g' hg'
    exact
      dualNormLe_of_mem_topExtension_zeroExtensionOn_subdifferential
        Q p φ L hx hsubgradient_bound hg'
  have hQ_convex : Convex ℝ Q := hφ_convex.1
  have hscaled_convex : ConvexOn ℝ Q (fun z : E ↦ L * p z) :=
    convexOn_scaledSeminorm Q p L hQ_convex hL_nonneg
  -- Route correction: the old generic disjunction helper forgot that the theorem only needs this
  -- theorem-owner-specific boundary/no-witness dual bound on `augmentedZeroExtensionOn`.
  by_cases hstrictRight : zeroExtensionOn Q φ x < L * p x
  · have hgScaledQ :
        g ∈ ∂[Q] ((fun z : E ↦ L * p z) : E → ℝ)(x) :=
      mem_subdifferentialWithin_right_of_mem_max_strictRight
        Q hQ_convex hφ_convex hscaled_convex hgQ hstrictRight
    have hgScaled :
        g ∈ ∂ (fun z : E ↦ (((L * p z : ℝ) : ℝ) : WithTop ℝ))(x) :=
      mem_subdifferential_scaledSeminorm_of_mem_subdifferentialWithin_scaledSeminorm_of_mem_augmentedZeroExtensionOn_subdifferential_nonleft
        Q p φ L hL_nonneg hx hnonleft hg hgScaledQ
    -- Once the current owner has been pushed to the ambient scaled branch, the standard dual bound
    -- finishes the strict-right case directly.
    exact dualNorm_le_of_mem_subdifferential_scaled_seminorm p L hL_nonneg hgScaled
  · have htie : zeroExtensionOn Q φ x = L * p x :=
      le_antisymm hnonleft (le_of_not_gt hstrictRight)
    let _ := hgTopMax
    let _ := hzeroTopBound
    let _ := htie
    -- TODO: the remaining blocker is now the tie-only extractor on the actual theorem owner.
    -- From `hgQ : g ∈ ∂[Q] max(zeroExtensionOn Q φ, L * p)(x)`, `htie`, and the empty feasible
    -- left-branch subdifferential `hφ_empty`, derive that `g` already lies in the constrained
    -- scaled-seminorm branch, then reuse the ambient bridge above.
    sorry

/-- Helper for Theorem 7.19: on the actual theorem owner, once the boundary/no-witness non-left
branch gives direct `p`-dual control of the ambient subgradient, the strict-positivity
inequality follows immediately. -/
lemma strictPositivityExpr_nonneg_of_nonleft_of_noFeasibleSubgradient
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : Q → ℝ) (L : ℝ) (hL_nonneg : 0 ≤ L)
    {x y g : E}
    (hx : x ∈ Q) (hy : y ∈ Q)
    (hφ_convex : ConvexOn ℝ Q (zeroExtensionOn Q φ))
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) → p.dualNorm g ≤ L)
    (hnonleft : zeroExtensionOn Q φ x ≤ L * p x)
    (hg : g ∈ ∂[Set.univ] (augmentedZeroExtensionOn Q p φ L)(x))
    (hφ_empty : ¬ (∂[Q] (zeroExtensionOn Q φ)(x)).Nonempty) :
    0 ≤ augmentedZeroExtensionOn Q p φ L y +
        augmentedZeroExtensionOn Q p φ L x +
        inner ℝ g (y - x) := by
  -- First isolate the theorem-owner-specific dual bound on the remaining boundary/no-witness
  -- branch.
  have hg_dual :
      p.dualNorm g ≤ L :=
    dualNormLe_of_mem_augmentedZeroExtensionOn_subdifferential_nonleft_of_noFeasibleSubgradient
      Q p φ L hL_nonneg hx hφ_convex hsubgradient_bound hnonleft hg hφ_empty
  -- Then rewrite the owner back to the generic max expression and finish by the dual-bound
  -- positivity lemma.
  simpa [augmentedZeroExtensionOn] using
    strictly_positive_expr_nonneg_of_dualNorm_le p (zeroExtensionOn Q φ) L hg_dual

/-- Source-side strict positivity for a function on `Q`, packaged as existence of an ambient
real-valued representative that is strictly positive on `Q` in the sense of Definition 7.81. -/
def StrictlyPositiveOnSubtype (Q : Set E) (f : Q → ℝ) : Prop :=
  ∃ F : E → ℝ,
    (∀ ⦃x : E⦄ (hx : x ∈ Q), F x = f ⟨x, hx⟩) ∧
      StrictlyPositiveOn Q F

/-- A source-side function on `Q` is strictly positive once one ambient representative agrees with
it on `Q` and satisfies Definition 7.81 there. -/
theorem StrictlyPositiveOnSubtype.of_strictlyPositiveOn
    {Q : Set E} {f : Q → ℝ} {F : E → ℝ}
    (hF : ∀ ⦃x : E⦄ (hx : x ∈ Q), F x = f ⟨x, hx⟩)
    (hStrict : StrictlyPositiveOn Q F) :
    StrictlyPositiveOnSubtype Q f :=
  ⟨F, hF, hStrict⟩

/-- Bridge API: a source-side strictly positive function on `Q` comes with an ambient
`StrictlyPositiveOn` representative. -/
theorem StrictlyPositiveOnSubtype.exists_strictlyPositiveOn
    {Q : Set E} {f : Q → ℝ} (hf : StrictlyPositiveOnSubtype Q f) :
    ∃ F : E → ℝ,
      (∀ ⦃x : E⦄ (hx : x ∈ Q), F x = f ⟨x, hx⟩) ∧
        StrictlyPositiveOn Q F :=
  hf

/-- Ambient representative helper for the source-facing Theorem 7.19 statement: the canonical
zero-extension representative of the augmented function is strictly positive on `Q`. -/
theorem strictlyPositiveOn_augmentedZeroExtensionOn
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : Q → ℝ) (L : ℝ)
    (hφ_convex : ConvexOn ℝ Q (zeroExtensionOn Q φ)) (hL_nonneg : 0 ≤ L)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄,
        x ∈ Q →
        g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) →
        p.dualNorm g ≤ L) :
    StrictlyPositiveOn Q (augmentedZeroExtensionOn Q p φ L) := by
  intro x y g hx hy hg
  have hboundWithin :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) → p.dualNorm g ≤ L := by
    intro x g hgQ
    exact hsubgradient_bound (mem_subdifferentialWithin_iff.mp hgQ).1 hgQ
  -- Split by the active branch of the augmented max at the current base point `x`.
  by_cases hstrictLeft : L * p x < zeroExtensionOn Q φ x
  · -- On the strict-left branch, the ambient max-subgradient already restricts to `φ`.
    simpa [augmentedZeroExtensionOn] using
      strictly_positive_expr_nonneg_of_mem_subdifferential_max_strictLeft
        Q p (zeroExtensionOn Q φ) L hL_nonneg hx hy hφ_convex hboundWithin hg hstrictLeft
  · have hnonleft : zeroExtensionOn Q φ x ≤ L * p x := by
      linarith
    by_cases hφ_nonempty : (∂[Q] (zeroExtensionOn Q φ)(x)).Nonempty
    · rcases hφ_nonempty with ⟨gφ, hgφ⟩
      -- One explicit feasible witness closes the remaining non-left branch through the existing
      -- ambient max-subgradient route.
      simpa [augmentedZeroExtensionOn] using
        strictPositivityExpr_nonneg_of_mem_maxSubdifferential
          Q p (zeroExtensionOn Q φ) L hL_nonneg hx hy hφ_convex hgφ hboundWithin hg
    · -- The stabilized frontier is now exactly the boundary/no-witness non-left case.
      exact
        strictPositivityExpr_nonneg_of_nonleft_of_noFeasibleSubgradient
          Q p φ L hL_nonneg hx hy hφ_convex hboundWithin hnonleft hg hφ_nonempty

/-- Theorem 7.19 (Strict positivity of the augmented function): if `φ : Q → ℝ` is convex on the
feasible set `Q` and every feasible constrained subgradient of `φ` has dual norm at most `L`,
then the source augmented function `x ↦ max (φ x) (L * p x)` is strictly positive on `Q` in the
sense of Definition 7.81. -/
theorem strictlyPositiveOn_max_of_subgradientWithin_dualNorm_le
    (Q : Set E) [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : Q → ℝ) (L : ℝ)
    (hφ_convex : ConvexOn ℝ Q (zeroExtensionOn Q φ)) (hL_nonneg : 0 ≤ L)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄,
        x ∈ Q →
        g ∈ ∂[Q] (zeroExtensionOn Q φ)(x) →
        p.dualNorm g ≤ L) :
    StrictlyPositiveOnSubtype Q (augmentedFunctionOn p φ L) := by
  -- Package the ambient zero-extension theorem into the source-side subtype owner.
  refine
    StrictlyPositiveOnSubtype.of_strictlyPositiveOn
      (F := augmentedZeroExtensionOn Q p φ L)
      (f := augmentedFunctionOn p φ L)
      ?_ ?_
  · intro x hx
    -- The canonical ambient representative agrees with the source max objective on feasible
    -- points by construction.
    simpa using (augmentedZeroExtensionOn_apply_of_mem (p := p) (φ := φ) (L := L) hx)
  · -- Feed the source hypotheses into the ambient theorem.
    exact
      strictlyPositiveOn_augmentedZeroExtensionOn
        Q p φ L hφ_convex hL_nonneg hsubgradient_bound
