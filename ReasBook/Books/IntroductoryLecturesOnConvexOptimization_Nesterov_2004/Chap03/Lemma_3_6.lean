/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology WithTopConvexAnalysis

universe u

/-
Lemma 3.6 lies in the chapter's extended-valued constrained-subdifferential domain.

Sampled owner-style declarations:
- `∂[Q] f(x)` / `constrainedSubdifferential` in `Definition_3_1_5`, the source-facing local
  subgradient owner;
- `mem_constrainedSubdifferential_iff` in `Definition_3_1_5`, the atomic membership bridge;
- `withTopRealPart` in `Definition_3_3`, the canonical finite-valued representative on the
  effective domain;
- `ClosedConvexOn` in `Definition_3_1_1_5`, a downstream bridge that packages convexity,
  lower-semicontinuity, and finiteness into epigraph language when extra closedness is available.

Best owner abstraction:
- the constrained-subdifferential owner `∂[Q] f(x)` together with the canonical conclusion
  surfaces `ConvexOn ℝ Q (withTopRealPart f)` and
  `LowerSemicontinuousOn (withTopRealPart f) Q`.

Primitive data:
- the feasible set `Q`;
- the `WithTop ℝ`-valued objective `f`;
- pointwise nonemptiness of `∂[Q] f(x)` on `Q`;
- convexity of `Q`, needed only for the convexity conclusion.

Derived API:
- `convexOn_of_constrainedSubdifferential_nonempty`;
- `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`.

Source/core/bridge triage:
- source-facing: Lemma 3.6's convexity and lower-semicontinuity consequences;
- core/canonical: `constrainedSubdifferential`, `mem_constrainedSubdifferential_iff`, and
  `withTopRealPart`;
- bridge/view: downstream repackaging into `ClosedConvexOn`.

The owner abstraction here is the constrained subdifferential itself, not a wrapper around its
epigraph consequences. Since the lower-semicontinuity proof uses only the supporting affine
minorant at each base point, convexity of `Q` is redundant for that second theorem and is removed
from its public API; only the convexity theorem keeps the convexity hypothesis.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (Q : Set E) (f : E → WithTop ℝ)

/-- Helper for Lemma 3.6: nonempty constrained subdifferentials force finiteness of `f` on `Q`. -/
-- Proof sketch: any witness `g ∈ ∂[Q] f(x)` already carries the domain fact `x ∈ dom f` in its
-- defining membership data.
lemma mem_dom_of_constrainedSubdifferential_nonempty
    (hsub : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) {x : E} (hx : x ∈ Q) :
    x ∈ dom f := by
  rcases hsub x hx with ⟨g, hg⟩
  exact (mem_constrainedSubdifferential_iff.mp hg).2.1

/-- Helper for Lemma 3.6: a constrained subgradient gives a real affine lower support inequality
for `withTopRealPart` at every finite point of `Q`. -/
-- Proof sketch: read the owner inequality from `mem_constrainedSubdifferential_iff`, then coerce
-- the finite endpoint values back and forth between `WithTop ℝ` and `ℝ`.
lemma withTopRealPart_le_of_mem_constrainedSubdifferential
    {x y g : E} (hg : g ∈ ∂[Q] f(x)) (hyQ : y ∈ Q) (hyDom : y ∈ dom f) :
    withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
  have hxDom : x ∈ dom f := (mem_constrainedSubdifferential_iff.mp hg).2.1
  have hsupport : f y ≥ f x + (inner ℝ g (y - x) : WithTop ℝ) :=
    (mem_constrainedSubdifferential_iff.mp hg).2.2 hyQ
  rw [← coe_withTopRealPart hyDom, ← coe_withTopRealPart hxDom] at hsupport
  exact_mod_cast hsupport

/-- Helper for Lemma 3.6: a constrained subgradient at `x` produces a continuous affine minorant,
so `withTopRealPart f` is lower semicontinuous within `Q` at `x`. -/
-- Proof sketch: compare `withTopRealPart f` to the affine function
-- `z ↦ withTopRealPart f x + ⟪g, z - x⟫`, which agrees with `withTopRealPart f x` at `x` and is
-- continuous. The subgradient inequality keeps `withTopRealPart f` above this affine minorant on
-- `Q`, so any strict lower bound at `x` persists along `Q`.
lemma lowerSemicontinuousWithinAt_of_mem_constrainedSubdifferential
    (hsub : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) {x g : E} (_hxQ : x ∈ Q) (hg : g ∈ ∂[Q] f(x)) :
    LowerSemicontinuousWithinAt (withTopRealPart f) Q x := by
  rw [lowerSemicontinuousWithinAt_iff]
  intro y hy
  let affine : E → ℝ := fun z ↦ withTopRealPart f x + inner ℝ g (z - x)
  have haffine_cont : ContinuousWithinAt affine Q x := by
    -- The supporting affine minorant is continuous, so strict lower bounds persist near `x`.
    have hcont : Continuous affine := by
      simpa [affine] using
        continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))
    exact hcont.continuousWithinAt
  have hbase : y < affine x := by
    simpa [affine] using hy
  have haffine_eventually : ∀ᶠ z in 𝓝[Q] x, y < affine z :=
    (lowerSemicontinuousWithinAt_iff.mp
      haffine_cont.lowerSemicontinuousWithinAt) y hbase
  filter_upwards [self_mem_nhdsWithin, haffine_eventually] with z hzQ hz
  have hzDom : z ∈ dom f :=
    mem_dom_of_constrainedSubdifferential_nonempty (Q := Q) (f := f) hsub hzQ
  have hminorant :
      affine z ≤ withTopRealPart f z :=
    withTopRealPart_le_of_mem_constrainedSubdifferential
      (Q := Q) (f := f) hg hzQ hzDom
  exact lt_of_lt_of_le hz hminorant

/-- Lemma 3.6 (1), generalized from the textbook `ℝⁿ` setting: if `Q` is convex and every
constrained subdifferential `∂_Q f(x)` with `x ∈ Q` is nonempty, then the finite-valued
representative of `f` is convex on `Q`. The
nonemptiness hypothesis already forces `f` to be finite on `Q`. -/
-- Proof sketch: fix `x₀, x₁ ∈ Q` and `θ ∈ [0, 1]`, and set `xθ = (1 - θ) • x₀ + θ • x₁`. Choose
-- `g ∈ ∂_Q f(xθ)`, apply the subgradient inequality to `y = x₀` and `y = x₁`, weight the two
-- inequalities by `1 - θ` and `θ`, and add. The inner-product term cancels because
-- `(1 - θ) • (x₀ - xθ) + θ • (x₁ - xθ) = 0`. Since membership in `∂_Q f(x)` already records
-- `x ∈ withTopEffectiveDomain f`, the nonemptiness hypothesis itself supplies the finiteness of
-- `f` on `Q`.
theorem convexOn_of_constrainedSubdifferential_nonempty
    (hQ_convex : Convex ℝ Q)
    (hsub : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) :
    ConvexOn ℝ Q (withTopRealPart f) := by
  refine ⟨hQ_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  have hzQ : z ∈ Q := hQ_convex hx hy ha hb hab
  have hxDom : x ∈ dom f :=
    mem_dom_of_constrainedSubdifferential_nonempty (Q := Q) (f := f) hsub hx
  have hyDom : y ∈ dom f :=
    mem_dom_of_constrainedSubdifferential_nonempty (Q := Q) (f := f) hsub hy
  rcases hsub z hzQ with ⟨g, hg⟩
  have hx_support :
      withTopRealPart f z + inner ℝ g (x - z) ≤ withTopRealPart f x :=
    withTopRealPart_le_of_mem_constrainedSubdifferential
      (Q := Q) (f := f) hg hx hxDom
  have hy_support :
      withTopRealPart f z + inner ℝ g (y - z) ≤ withTopRealPart f y :=
    withTopRealPart_le_of_mem_constrainedSubdifferential
      (Q := Q) (f := f) hg hy hyDom
  have hx_weighted :
      a * (withTopRealPart f z + inner ℝ g (x - z)) ≤ a * withTopRealPart f x :=
    mul_le_mul_of_nonneg_left hx_support ha
  have hy_weighted :
      b * (withTopRealPart f z + inner ℝ g (y - z)) ≤ b * withTopRealPart f y :=
    mul_le_mul_of_nonneg_left hy_support hb
  have hvec :
      a • (x - z) + b • (y - z) = 0 := by
    -- The weighted displacement from the convex combination point cancels exactly.
    calc
      a • (x - z) + b • (y - z)
          = (a • x + b • y) - (a + b) • z := by
              simp [sub_eq_add_neg, smul_add, add_smul, smul_neg, add_assoc, add_left_comm,
                add_comm]
      _ = z - z := by
            simp [z, hab]
      _ = 0 := sub_self z
  have hcancel :
      a * inner ℝ g (x - z) + b * inner ℝ g (y - z) = 0 := by
    -- Taking the inner product against the vanishing weighted displacement removes the linear term.
    calc
      a * inner ℝ g (x - z) + b * inner ℝ g (y - z)
          = inner ℝ g (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by rw [hvec, inner_zero_right]
  have hz_coeff :
      a * withTopRealPart f z + b * withTopRealPart f z = withTopRealPart f z := by
    calc
      a * withTopRealPart f z + b * withTopRealPart f z
          = (a + b) * withTopRealPart f z := by ring
      _ = withTopRealPart f z := by rw [hab, one_mul]
  -- Add the two support inequalities and use the cancellation identities to recover the Jensen
  -- bound at the convex combination point.
  have hadd :
      a * (withTopRealPart f z + inner ℝ g (x - z)) +
          b * (withTopRealPart f z + inner ℝ g (y - z))
        ≤ a * withTopRealPart f x + b * withTopRealPart f y :=
    add_le_add hx_weighted hy_weighted
  have hleft :
      a * (withTopRealPart f z + inner ℝ g (x - z)) +
          b * (withTopRealPart f z + inner ℝ g (y - z))
        = withTopRealPart f z := by
    calc
      a * (withTopRealPart f z + inner ℝ g (x - z)) +
          b * (withTopRealPart f z + inner ℝ g (y - z))
          = (a * withTopRealPart f z + b * withTopRealPart f z) +
              (a * inner ℝ g (x - z) + b * inner ℝ g (y - z)) := by
                ring
      _ = withTopRealPart f z + 0 := by rw [hz_coeff, hcancel]
      _ = withTopRealPart f z := by ring
  calc
    withTopRealPart f (a • x + b • y) = withTopRealPart f z := by rfl
    _ = a * (withTopRealPart f z + inner ℝ g (x - z)) +
          b * (withTopRealPart f z + inner ℝ g (y - z)) := hleft.symm
    _ ≤ a * withTopRealPart f x + b * withTopRealPart f y := hadd
    _ = a • withTopRealPart f x + b • withTopRealPart f y := by rfl

/-- Lemma 3.6 (2), generalized from the textbook `ℝⁿ` setting: if every constrained
subdifferential `∂_Q f(x)` with `x ∈ Q` is nonempty, then the finite-valued representative of `f`
is lower semicontinuous on `Q`; again the nonemptiness hypothesis already forces finiteness on
`Q`. Unlike part (1), no convexity hypothesis on `Q` is needed. -/
-- Proof sketch: fix `x ∈ Q` and choose `g ∈ ∂_Q f(x)`. For every `y ∈ Q`, the subgradient
-- inequality gives `withTopRealPart f x + ⟪g, y - x⟫ ≤ withTopRealPart f y`. Since the affine
-- minorant is continuous, passing to the limit along points of `Q` converging to `x` yields the
-- lower semicontinuity inequality at `x` within `Q`.
theorem lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty
    (hsub : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) :
    LowerSemicontinuousOn (withTopRealPart f) Q := by
  rw [lowerSemicontinuousOn_iff]
  intro x hxQ
  rcases hsub x hxQ with ⟨g, hg⟩
  -- Each point of `Q` has a supporting affine minorant, and that local support is enough for
  -- lower semicontinuity within `Q` at the base point.
  exact lowerSemicontinuousWithinAt_of_mem_constrainedSubdifferential
    (Q := Q) (f := f) hsub hxQ hg

end

end
