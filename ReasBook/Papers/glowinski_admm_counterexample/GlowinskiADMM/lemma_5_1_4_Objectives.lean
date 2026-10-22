/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.theorem_2_1_4_ADMM
public import glowinski_admm_counterexample.ReasLib.Convex.ExtendedReal
public import Mathlib.Data.EReal.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- A real objective is smoothly strongly convex when it has a positive strong-convexity
modulus, is continuously differentiable, and has a globally Lipschitz derivative. -/
def IsSmoothStronglyConvex {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) : Prop :=
  ∃ μ : ℝ, ∃ L : NNReal, 0 < μ ∧ StrongConvexOn Set.univ μ f ∧
    ContDiff ℝ 1 f ∧ LipschitzWith L (fderiv ℝ f)

/-- Smooth strong convexity exposes its modulus and derivative Lipschitz constant. -/
theorem smoothStronglyConvex_iff {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} :
    IsSmoothStronglyConvex f ↔
      ∃ μ : ℝ, ∃ L : NNReal, 0 < μ ∧ StrongConvexOn Set.univ μ f ∧
        ContDiff ℝ 1 f ∧ LipschitzWith L (fderiv ℝ f) := by
  rfl

/-- Both unit-penalty consensus ADMM block objectives have a unique finite global
minimizer for every fixed value of the other block and multiplier. -/
def HasUniqueBlockMinimizers {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f g : E → EReal) : Prop :=
  (∀ y dual, ∃! x,
      f x ≠ ⊤ ∧ f x ≠ ⊥ ∧
        ∀ z,
          f x + ((inner ℝ dual (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) ≤
            f z + ((inner ℝ dual (z - y) + ‖z - y‖ ^ 2 / 2 : ℝ) : EReal)) ∧
    ∀ x dual, ∃! y,
      g y ≠ ⊤ ∧ g y ≠ ⊥ ∧
        ∀ z,
          g y + ((inner ℝ dual (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) ≤
            g z + ((inner ℝ dual (x - z) + ‖x - z‖ ^ 2 / 2 : ℝ) : EReal)

/-- Global uniqueness of the two block minimizers expands to the two augmented
objective minimization statements. -/
theorem uniqueBlockMinimizers_iff {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f g : E → EReal} :
    HasUniqueBlockMinimizers f g ↔
      (∀ y dual, ∃! x,
          f x ≠ ⊤ ∧ f x ≠ ⊥ ∧
            ∀ z,
              f x + ((inner ℝ dual (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) ≤
                f z + ((inner ℝ dual (z - y) + ‖z - y‖ ^ 2 / 2 : ℝ) : EReal)) ∧
        ∀ x dual, ∃! y,
          g y ≠ ⊤ ∧ g y ≠ ⊥ ∧
            ∀ z,
              g y + ((inner ℝ dual (x - y) + ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) ≤
                g z + ((inner ℝ dual (x - z) + ‖x - z‖ ^ 2 / 2 : ℝ) : EReal) := by
  rfl

/-- A finite unique minimizer also excludes nonfinite competing minimizers. -/
private theorem unique_of_unique_finite_augmented {E : Type*}
    (f : E → EReal) (a : E → ℝ)
    (h : ∃! p, f p ≠ ⊤ ∧ f p ≠ ⊥ ∧
      ∀ t, f p + (a p : EReal) ≤ f t + (a t : EReal))
    {x z : E} (hx : ∀ t, f x + (a x : EReal) ≤ f t + (a t : EReal))
    (hz : f z + (a z : EReal) ≤ f x + (a x : EReal)) : z = x := by
  obtain ⟨p, hp, huniq⟩ := h
  have identify (t : E)
      (ht : ∀ v, f t + (a t : EReal) ≤ f v + (a v : EReal)) : t = p := by
    have heq : f t + (a t : EReal) = f p + (a p : EReal) :=
      le_antisymm (ht p) (hp.2.2 t)
    have htop : f t + (a t : EReal) ≠ ⊤ := by
      rw [heq]
      exact EReal.add_ne_top hp.1 (EReal.coe_ne_top _)
    have hbot : f t + (a t : EReal) ≠ ⊥ := by
      rw [heq]
      exact EReal.add_ne_bot_iff.mpr ⟨hp.2.1, EReal.coe_ne_bot _⟩
    exact huniq t ⟨(EReal.add_ne_top_iff_ne_top_left
      (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp htop,
      (EReal.add_ne_bot_iff.mp hbot).1, ht⟩
  exact (identify z (fun t ↦ hz.trans (hx t))).trans (identify x hx).symm

/-- Globally unique block minimizers make every update of any supplied trajectory unique. -/
theorem HasUniqueBlockMinimizers.hasUniqueUpdates {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f g : E → EReal}
    {γ : ℝ} {x y dual : ℕ → E} (hunique : HasUniqueBlockMinimizers f g)
    (htrajectory : IsTrajectory γ f g x y dual) : HasUniqueUpdates f g x y dual := by
  intro k
  constructor
  · intro z hz
    exact unique_of_unique_finite_augmented f
      (fun v ↦ inner ℝ (dual k) (v - y k) + ‖v - y k‖ ^ 2 / 2)
      (hunique.1 (y k) (dual k)) (htrajectory k).1 hz
  · intro z hz
    exact unique_of_unique_finite_augmented g
      (fun v ↦ inner ℝ (dual k) (x (k + 1) - v) + ‖x (k + 1) - v‖ ^ 2 / 2)
      (hunique.2 (x (k + 1)) (dual k)) (htrajectory k).2.1 hz

/-- A consensus KKT triple is unique when every other KKT triple agrees in all
three components. -/
def IsUniqueKKT {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E → EReal) (x y dual : E) : Prop :=
  IsKKT f g x y dual ∧
    ∀ x' y' dual', IsKKT f g x' y' dual' → x' = x ∧ y' = y ∧ dual' = dual

/-- Unique KKT status is the KKT property together with componentwise uniqueness. -/
theorem uniqueKKT_iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → EReal} {x y dual : E} :
    IsUniqueKKT f g x y dual ↔
      IsKKT f g x y dual ∧
        ∀ x' y' dual', IsKKT f g x' y' dual' → x' = x ∧ y' = y ∧ dual' = dual := by
  rfl

/-- A unique KKT triple is in particular a KKT triple. -/
theorem IsUniqueKKT.isKKT {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → EReal} {x y dual : E} (h : IsUniqueKKT f g x y dual) :
    IsKKT f g x y dual := by
  exact h.1

end ConsensusADMM
