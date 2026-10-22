/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 7.58 lies in the chapter's barrier-subgradient / dual-seminorm domain on real
inner-product spaces.

Sampled owner-style declarations:
- `Seminorm.IsNorm` in `Chap02/Definition_2_5`
- `Seminorm.dualNorm` in `Chap02/Definition_2_5`
- `Seminorm.dualNorm_apply` in `Chap02/Definition_2_5`
- `constrainedSubdifferential` and `∂[Q] f(x)` in `Chap03/Definition_3_1_5`

Best owner abstraction:
- source-facing: Definition 7.58's barrier subgradient class together with the sequences `λₖ`
  and `βₖ`
- core/canonical: `Seminorm.dualNorm` and `constrainedSubdifferential`
- bridge/view: the coercion `fun y ↦ (f y : WithTop ℝ)` into the Chapter 3 owner surface

Primitive data:
- the feasible set `P` and distinguished subset `P₀`
- the point-indexed norm family `pointNorm : P₀ → Seminorm ℝ E`
- the separation proofs `hpointNorm : ∀ x, Seminorm.IsNorm (pointNorm x)`

Derived API:
- the membership expansion of the barrier subgradient class

The previous file duplicated the chapter owners `Seminorm.IsNorm`, `Seminorm.dualNorm`, and
`constrainedSubdifferential`. This refinement keeps the source-facing barrier notion but moves its
primitive convex-analysis data to those canonical owners, and it quantifies directly over `x : P₀`
rather than over ambient points plus a separate membership proof. The dual `‖·‖ₓ*`-bound uses
the canonical owner `(pointNorm x).dualNorm` directly instead of a parallel local bridge. -/

/-- Definition 7.58: for a feasible set `P ⊆ E`, a distinguished subset `P₀`, and a norm `‖·‖ₓ`
on `E` for each `x ∈ P₀`, `barrierSubgradientClass P P₀ pointNorm hpointNorm M` is the set
`𝓑_M(P)` of real-valued functions on `E` whose constrained subdifferential over `P` is
nonempty at every `x ∈ P₀` with some subgradient having `‖·‖ₓ*`-norm at most `M`. -/
def barrierSubgradientClass
    (P P0 : Set E) (pointNorm : P0 → Seminorm ℝ E)
    (hpointNorm : ∀ x : P0, Seminorm.IsNorm (pointNorm x)) (M : NNReal) :
    Set (E → ℝ) :=
  {f | ∀ x : P0,
      ∃ g : E,
        let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
        g ∈ ∂[P] (fun y ↦ (f y : WithTop ℝ)) (x) ∧
          (pointNorm x).dualNorm g ≤ (M : ℝ)}

-- Proof sketch: unfold `barrierSubgradientClass`; membership is exactly the pointwise bounded
-- constrained-subgradient condition over the distinguished subset `P₀`.
/-- Membership in `barrierSubgradientClass P P₀ pointNorm hpointNorm M` means that each
`x ∈ P₀` admits a constrained subgradient over `P` whose dual `‖·‖ₓ*`-norm is at most `M`; the
feasibility condition `x ∈ P` is already part of the constrained-subdifferential owner. -/
theorem mem_barrierSubgradientClass_iff
    {P P0 : Set E} {pointNorm : P0 → Seminorm ℝ E}
    {hpointNorm : ∀ x : P0, Seminorm.IsNorm (pointNorm x)} {M : NNReal} {f : E → ℝ} :
    f ∈ barrierSubgradientClass P P0 pointNorm hpointNorm M ↔
      ∀ x : P0,
        ∃ g : E,
          let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
          g ∈ ∂[P] (fun y ↦ (f y : WithTop ℝ)) (x) ∧
            (pointNorm x).dualNorm g ≤ (M : ℝ) := by
  rfl

/-- The sequence `λₖ` attached to the barrier subgradient scheme is constantly equal to `1`. -/
def barrierSubgradientLambda : ℕ → ℝ :=
  fun _ ↦ 1

-- Proof sketch: unfold `barrierSubgradientLambda`; the sequence is defined to be constant.
/-- The sequence `barrierSubgradientLambda` satisfies `λₖ = 1` for every `k ≥ 0`. -/
theorem barrierSubgradientLambda_apply (k : ℕ) :
    barrierSubgradientLambda k = 1 := by
  rfl

/-- The sequence `βₖ` from Definition 7.58, written so that `β₀ = β₁` and for `k ≥ 1` one has
`βₖ = M (1 + √(k / ν))`. -/
def barrierSubgradientBeta (M : NNReal) (ν : {ν : ℝ // 0 < ν}) : ℕ → ℝ :=
  fun k ↦ (M : ℝ) * (1 + Real.sqrt (((max k 1 : ℕ) : ℝ) / (ν : ℝ)))

-- Proof sketch: unfold `barrierSubgradientBeta` and simplify `max 0 1 = 1`.
/-- The sequence `barrierSubgradientBeta` satisfies `β₀ = β₁`. -/
theorem barrierSubgradientBeta_zero_eq_one
    (M : NNReal) (ν : {ν : ℝ // 0 < ν}) :
    barrierSubgradientBeta M ν 0 = barrierSubgradientBeta M ν 1 := by
  simp [barrierSubgradientBeta]

-- Proof sketch: unfold `barrierSubgradientBeta`; for `k ≥ 1`, the identity `max k 1 = k`
-- rewrites the definition into the textbook formula.
/-- For `k ≥ 1`, `barrierSubgradientBeta M ν k` is exactly
`M (1 + √(k / ν))`. -/
theorem barrierSubgradientBeta_of_one_le
    (M : NNReal) (ν : {ν : ℝ // 0 < ν}) {k : ℕ} (hk : 1 ≤ k) :
    barrierSubgradientBeta M ν k =
      (M : ℝ) * (1 + Real.sqrt ((k : ℝ) / (ν : ℝ))) := by
  simp [barrierSubgradientBeta, max_eq_left hk]

end
