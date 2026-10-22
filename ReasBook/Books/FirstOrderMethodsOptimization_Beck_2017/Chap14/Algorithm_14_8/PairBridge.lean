/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8

universe u

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedSpace ℝ E1]
variable [NormedAddCommGroup E2] [NormedSpace ℝ E2]

/-- The `Fin 2` smooth-term view of a pair objective `f(x₁, x₂)` from Algorithm 14.8. -/
abbrev twoBlockAlternatingMinimizationSmoothTerm
    (f : E1 × E2 → ℝ) :
    ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i) → ℝ :=
  fun x ↦ f (x 0, x 1)

/-- The `Fin 2` penalty family attached to the pair penalties `(g₁, g₂)` from Algorithm 14.8. -/
abbrev twoBlockAlternatingMinimizationPenalties
    (g1 : E1 → EReal) (g2 : E2 → EReal) :
    ∀ i : Fin 2, two_block_alternating_minimization_space E1 E2 i → EReal :=
  Fin.cases g1 fun _ ↦ g2

/-- The canonical `Fin 2` optimal-set view of a pair-valued optimal set. -/
abbrev twoBlockAlternatingMinimizationOptimalSet
    (XStar : Set (E1 × E2)) :
    Set ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i) :=
  {x | (x 0, x 1) ∈ XStar}

/-- The pairwise smoothness moduli `L₁` and `L₂` induce the conservative global `Fin 2`
smoothness constant `max {L₁, L₂}` used by the Chapter 14 convex-rate owner. -/
abbrev twoBlockAlternatingMinimizationGlobalSmoothness
    (L1 L2 : PosReal) : NNReal :=
  max (PosReal.toNNReal L1) (PosReal.toNNReal L2)

/-- The first-block partial infimum `φ₁(y₁) = inf_z₂ F(y₁, z₂)` for the pair objective from
Algorithm 14.8. -/
noncomputable abbrev twoBlockX1PartialInfimum
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal) :
    E1 → EReal :=
  fun y1 ↦
    sInf <| Set.range fun z2 : E2 ↦
      two_block_alternating_minimization_objective f.toEReal g1 g2 (y1, z2)

/-- The second-block partial infimum `φ₂(y₂) = inf_z₁ F(z₁, y₂)` for the pair objective from
Algorithm 14.8. -/
noncomputable abbrev twoBlockX2PartialInfimum
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal) :
    E2 → EReal :=
  fun y2 ↦
    sInf <| Set.range fun z1 : E1 ↦
      two_block_alternating_minimization_objective f.toEReal g1 g2 (z1, y2)

/-- The first inactive marginal `η₁(y₁) = inf_z₂ (f(y₁, z₂) + g₂(z₂))` used in the source proof
of Theorem 14.8. -/
noncomputable abbrev twoBlockX1InactiveMarginal
    (f : E1 × E2 → ℝ) (g2 : E2 → EReal) :
    E1 → EReal :=
  fun y1 ↦
    sInf <| Set.range fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2

/-- The second inactive marginal `η₂(y₂) = inf_z₁ (f(z₁, y₂) + g₁(z₁))` used in the source proof
of Theorem 14.8. -/
noncomputable abbrev twoBlockX2InactiveMarginal
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) :
    E2 → EReal :=
  fun y2 ↦
    sInf <| Set.range fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
@[simp] theorem twoBlockX1PartialInfimum_apply
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal) (y1 : E1) :
    twoBlockX1PartialInfimum f g1 g2 y1 =
      sInf (Set.range fun z2 : E2 ↦
        two_block_alternating_minimization_objective f.toEReal g1 g2 (y1, z2)) :=
  rfl

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
@[simp] theorem twoBlockX2PartialInfimum_apply
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal) (y2 : E2) :
    twoBlockX2PartialInfimum f g1 g2 y2 =
      sInf (Set.range fun z1 : E1 ↦
        two_block_alternating_minimization_objective f.toEReal g1 g2 (z1, y2)) :=
  rfl

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
@[simp] theorem twoBlockX1InactiveMarginal_apply
    (f : E1 × E2 → ℝ) (g2 : E2 → EReal) (y1 : E1) :
    twoBlockX1InactiveMarginal f g2 y1 =
      sInf (Set.range fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2) :=
  rfl

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
@[simp] theorem twoBlockX2InactiveMarginal_apply
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (y2 : E2) :
    twoBlockX2InactiveMarginal f g1 y2 =
      sInf (Set.range fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1) :=
  rfl

instance twoBlockAlternatingMinimizationSpaceNormedAddCommGroup :
    (i : Fin 2) → NormedAddCommGroup (two_block_alternating_minimization_space E1 E2 i)
  | 0 => by
      simpa [two_block_alternating_minimization_space] using
        (inferInstance : NormedAddCommGroup E1)
  | 1 => by
      simpa [two_block_alternating_minimization_space] using
        (inferInstance : NormedAddCommGroup E2)

instance twoBlockAlternatingMinimizationSpaceNormedSpace :
    (i : Fin 2) → NormedSpace ℝ (two_block_alternating_minimization_space E1 E2 i)
  | 0 => by
      simpa [two_block_alternating_minimization_space] using
        (inferInstance : NormedSpace ℝ E1)
  | 1 => by
      simpa [two_block_alternating_minimization_space] using
        (inferInstance : NormedSpace ℝ E2)

variable {E : Type u} {V : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If the smooth term `h` is jointly convex and the inactive penalty `q` is convex, then the
split objective `H (x, v) = h(x, v) + q(v)` is convex on the product space. -/
lemma joint_convex_split_objective_is_convex_function
    {h : E × V → ℝ} {q : V → EReal}
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hq_ne_bot : ∀ v : V, q v ≠ ⊥)
    (hq_convex : is_convex_function q) :
    is_convex_function (fun p : E × V ↦ (((h p : ℝ) : EReal)) + q p.2) := by
  have hh_pair : is_convex_function (fun p : E × V ↦ (((h p : ℝ) : EReal))) := by
    simpa using Function.toEReal_isConvexFunction hh_convex
  have hq_pair : is_convex_function (fun p : E × V ↦ q p.2) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := q)
        hq_convex
        (LinearMap.snd ℝ E V)
        (0 : V)
  have hh_pair_ne_bot : ∀ p : E × V, (((h p : ℝ) : EReal)) ≠ ⊥ := by
    intro p
    simp
  have hq_pair_ne_bot : ∀ p : E × V, q p.2 ≠ ⊥ := fun p ↦ hq_ne_bot p.2
  simpa [Pi.add_apply] using
    is_convex_function_pointwise_add hh_pair hq_pair hh_pair_ne_bot hq_pair_ne_bot

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Reattaching a frozen inactive penalty preserves the active-slice support inequality. -/
lemma active_slice_support_with_frozen_inactive_penalty
    {h : E × V → ℝ} {q : V → EReal} {x0 : E} {v0 : V} {g : Module.Dual ℝ E}
    (hactive_subgrad :
      is_subgradient_at (fun x : E ↦ (((h (x, v0) : ℝ) : EReal))) x0 g) :
    ∀ y : E,
      (((h (y, v0) : ℝ) : EReal)) + q v0 ≥
        ((((h (x0, v0) : ℝ) : EReal)) + q v0) + (g (y - x0) : EReal) := by
  intro y
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_right (hactive_subgrad.2 y) (q v0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A zero inactive-slice subgradient is equivalent to the corresponding frozen active-point
support inequality. -/
lemma inactive_slice_support_of_zero_subgradient
    {h : E × V → ℝ} {q : V → EReal} {x0 : E} {v0 : V}
    (hzero_subgrad :
      (0 : Module.Dual ℝ V) ∈
        subdifferential (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v) v0) :
    ∀ v : V,
      (((h (x0, v) : ℝ) : EReal)) + q v ≥
        (((h (x0, v0) : ℝ) : EReal)) + q v0 := by
  intro v
  simpa using hzero_subgrad.2 v

/-- An active-slice subgradient together with a zero inactive-slice subgradient yields the two
staged slice-support inequalities used in the two-block analysis. -/
lemma pair_support_of_active_slice_subgradient_and_inactive_zero_subgradient
    {h : E × V → ℝ} {q : V → EReal} {x0 : E} {v0 : V} {g : Module.Dual ℝ E}
    (hH_convex :
      is_convex_function (fun p : E × V ↦ (((h p : ℝ) : EReal)) + q p.2))
    (hactive_subgrad :
      is_subgradient_at (fun x : E ↦ (((h (x, v0) : ℝ) : EReal))) x0 g)
    (hzero_subgrad :
      (0 : Module.Dual ℝ V) ∈
        subdifferential (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v) v0) :
    (∀ y : E,
      (((h (y, v0) : ℝ) : EReal)) + q v0 ≥
        ((((h (x0, v0) : ℝ) : EReal)) + q v0) + (g (y - x0) : EReal)) ∧
      ∀ v : V,
        (((h (x0, v) : ℝ) : EReal)) + q v ≥
          (((h (x0, v0) : ℝ) : EReal)) + q v0 := by
  let _ := hH_convex
  have hactive_support :
      ∀ y : E,
        (((h (y, v0) : ℝ) : EReal)) + q v0 ≥
          ((((h (x0, v0) : ℝ) : EReal)) + q v0) + (g (y - x0) : EReal) :=
    active_slice_support_with_frozen_inactive_penalty
      (q := q)
      (x0 := x0)
      (v0 := v0)
      (g := g)
      hactive_subgrad
  have hinactive_support :
      ∀ v : V,
        (((h (x0, v) : ℝ) : EReal)) + q v ≥
          (((h (x0, v0) : ℝ) : EReal)) + q v0 :=
    inactive_slice_support_of_zero_subgradient
      (h := h)
      (q := q)
      (x0 := x0)
      (v0 := v0)
      hzero_subgrad
  exact ⟨hactive_support, hinactive_support⟩

end
