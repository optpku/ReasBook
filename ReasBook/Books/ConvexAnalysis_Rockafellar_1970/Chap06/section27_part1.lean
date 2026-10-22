/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section02_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part18

section Chap06
section Section27

/-- Definition 6.27.1 (Sublevel set): for an extended-real-valued function
`f : ℝ^n → (-∞, +∞]` and `α ∈ ℝ`, the `α`-sublevel set `lev_α f` is
`{x ∈ ℝ^n | f x ≤ α}`. -/
def sublevelSet {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | f x ≤ (α : WithTop ℝ)}

/-- Definition 6.27.2 (Infimum of a function): for an extended-real-valued function
`f : ℝ^n → (-∞, +∞]`, the infimum `inf f` is the infimum in `[-∞, +∞]` of the set of values
`{f x | x ∈ ℝ^n}`, viewed in `[-∞, +∞]`, equivalently the greatest lower bound of those values. -/
noncomputable def functionInfimum {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : WithBot (WithTop ℝ) :=
  sInf (Set.range fun x => ((f x : WithTop ℝ) : WithBot (WithTop ℝ)))

/-- Definition 6.27.3 (Minimum set): for an extended-real-valued function
`f : ℝ^n → (-∞, +∞]`, the minimum set is the set of minimizers,
namely `{x ∈ ℝ^n | f x = inf f}`, with `f x` viewed in `[-∞, +∞]`. -/
def minimumSet {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set (Fin n → ℝ) :=
  {x | ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) = functionInfimum f}

/-- An extended-real-valued function on `ℝ^n` is convex when its epigraph is a convex subset
of `ℝ^n × ℝ`. -/
def IsConvexFunction {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Prop :=
  Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)}

/-- Lift a `WithTop ℝ`-valued function to an `EReal`-valued function by viewing each value in
`(-∞, +∞]` as an extended real with no additional `-∞` values introduced. -/
def withTopFunctionToEReal {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : (Fin n → ℝ) → EReal :=
  fun x => (WithBot.some (f x) : EReal)

/-- Definition 6.27.9 (Epigraph): for an extended-real-valued function
`h : ℝ^n → (-∞, +∞]`, the epigraph `epi h` is the subset of `ℝ^(n+1)` consisting of the
pairs `(x, μ)` with `h x ≤ μ`. In Lean, `ℝ^(n+1)` is modeled as `(Fin n → ℝ) × ℝ`. -/
def epigraphWithTop {n : ℕ} (h : (Fin n → ℝ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p | h p.1 ≤ (p.2 : WithTop ℝ)}

-- Proof sketch: view the sublevel set as the horizontal slice of the epigraph
-- at height `α`; convexity of the epigraph then implies convexity of this slice.
/-- Helper for Proposition 6.27.1: membership in the `α`-sublevel set is the same as
membership in the epigraph at height `α`. -/
lemma helperForProposition_6_27_1_mem_epigraphWithTop_iff {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} {α : ℝ} :
    x ∈ sublevelSet f α ↔ (x, α) ∈ epigraphWithTop f := by
  -- Unfold both sets to expose the same inequality.
  rfl

/-- Helper for Proposition 6.27.1: an affine combination of two points with common height `α`
still has height `α` when the coefficients sum to `1`. -/
lemma helperForProposition_6_27_1_affineCombo_same_height {n : ℕ}
    {x y : Fin n → ℝ} {a b α : ℝ} (hab : a + b = 1) :
    a • (x, α) + b • (y, α) = (a • x + b • y, α) := by
  -- Compare the product coordinates separately.
  ext
  · rfl
  · calc
      a • α + b • α = (a + b) * α := by
        simpa [smul_eq_mul] using (add_mul a b α).symm
      _ = α := by simp [hab]

/-- Helper for Proposition 6.27.1: convexity of the function is exactly convexity of its
epigraph written with the dedicated definition `epigraphWithTop`. -/
lemma helperForProposition_6_27_1_convex_epigraphWithTop_of_IsConvexFunction {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf : IsConvexFunction f) :
    Convex ℝ (epigraphWithTop f) := by
  -- This is only a definitional repackaging of `IsConvexFunction`.
  simpa [IsConvexFunction, epigraphWithTop] using hf

/-- Helper for Proposition 6.27.1: once the epigraph is convex, each horizontal slice at
height `α` is convex, so the corresponding sublevel set is convex. -/
lemma helperForProposition_6_27_1_convex_sublevelSet_of_convex_epigraphWithTop {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (h_epigraph : Convex ℝ (epigraphWithTop f)) (α : ℝ) :
    Convex ℝ (sublevelSet f α) := by
  intro x hx y hy a b ha hb hab
  -- Lift both sublevel-set points to the height-`α` slice of the epigraph.
  have hx_epigraph : (x, α) ∈ epigraphWithTop f :=
    (helperForProposition_6_27_1_mem_epigraphWithTop_iff).mp hx
  have hy_epigraph : (y, α) ∈ epigraphWithTop f :=
    (helperForProposition_6_27_1_mem_epigraphWithTop_iff).mp hy
  -- Convexity of the epigraph keeps the affine combination inside the same epigraph.
  have h_combo : a • (x, α) + b • (y, α) ∈ epigraphWithTop f :=
    h_epigraph hx_epigraph hy_epigraph ha hb hab
  -- Rewrite the product-space affine combination to expose the unchanged height `α`.
  have h_same_height : (a • x + b • y, α) ∈ epigraphWithTop f := by
    rw [← helperForProposition_6_27_1_affineCombo_same_height hab]
    exact h_combo
  -- Return from the epigraph slice to the original sublevel-set formulation.
  exact (helperForProposition_6_27_1_mem_epigraphWithTop_iff).mpr h_same_height

/-- Proposition 6.27.1 (Convexity of sublevel sets): if
`f : ℝ^n → (-∞, +∞]` is a convex function, then for every `α ∈ ℝ`
the sublevel set `sublevelSet f α = {x | f x ≤ α}` is convex. -/
theorem convex_sublevelSet {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ}
    (hf : IsConvexFunction f) (α : ℝ) :
    Convex ℝ (sublevelSet f α) := by
  -- First package convexity of the function as convexity of its epigraph.
  have h_epigraph : Convex ℝ (epigraphWithTop f) :=
    helperForProposition_6_27_1_convex_epigraphWithTop_of_IsConvexFunction hf
  -- Then take the horizontal slice of that convex epigraph at height `α`.
  exact helperForProposition_6_27_1_convex_sublevelSet_of_convex_epigraphWithTop h_epigraph α

-- Proof sketch: a closed convex function is in particular lower semicontinuous, and
-- lower semicontinuity implies that every real sublevel set `{x | f x ≤ α}` is closed.
/-- Helper for Proposition 6.27.2: the real sublevel set is the preimage of the lower interval
`(-∞, α]` in `WithTop ℝ`. -/
lemma helperForProposition_6_27_2_sublevelSet_eq_preimage_Iic {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (α : ℝ) :
    sublevelSet f α = f ⁻¹' Set.Iic (α : WithTop ℝ) := by
  -- Both sides are definitionally the same set of points satisfying `f x ≤ α`.
  rfl

/-- Helper for Proposition 6.27.2: a lower semicontinuous `WithTop ℝ`-valued function has
closed preimages of lower closed rays `(-∞, α]`. -/
lemma helperForProposition_6_27_2_isClosed_preimage_Iic {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf_closed : LowerSemicontinuous f) (α : ℝ) :
    IsClosed (f ⁻¹' Set.Iic (α : WithTop ℝ)) := by
  -- Apply the standard lower-semicontinuity theorem to the lower closed ray at level `α`.
  exact hf_closed.isClosed_preimage (α : WithTop ℝ)

/-- Helper for Proposition 6.27.2: lower semicontinuity alone already forces every real
sublevel set of `f` to be closed. -/
lemma helperForProposition_6_27_2_isClosed_sublevelSet_of_lsc {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf_closed : LowerSemicontinuous f) (α : ℝ) :
    IsClosed (sublevelSet f α) := by
  -- Rewrite the sublevel set into the exact preimage shape used by the semicontinuity lemma.
  rw [helperForProposition_6_27_2_sublevelSet_eq_preimage_Iic]
  -- Then invoke the dedicated preimage-closedness helper for the lower ray `(-∞, α]`.
  exact helperForProposition_6_27_2_isClosed_preimage_Iic hf_closed α

/-- Proposition 6.27.2 (Closedness of sublevel sets): if
`f : ℝ^n → (-∞, +∞]` is a closed convex function, then for every `α ∈ ℝ`
the sublevel set `sublevelSet f α = {x | f x ≤ α}` is closed. -/
theorem isClosed_sublevelSet_of_closed_convexFunction {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf_closed : LowerSemicontinuous f)
    (hf_convex : IsConvexFunction f) (α : ℝ) :
    IsClosed (sublevelSet f α) := by
  -- Keep the convexity hypothesis in scope because it is part of the textbook statement,
  -- even though lower semicontinuity is the only ingredient used in this argument.
  have _ : IsConvexFunction f := hf_convex
  -- Closedness of the sublevel set follows from lower semicontinuity; convexity is stronger
  -- than what this particular step needs.
  exact helperForProposition_6_27_2_isClosed_sublevelSet_of_lsc hf_closed α

/-- The effective domain of a `(-∞, +∞]`-valued function on `ℝ^n` is the set of points where the
function is finite. -/
def effectiveDomainWithTop {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set (Fin n → ℝ) :=
  {x | f x < (⊤ : WithTop ℝ)}

/-- Definition 6.27.4 (Direction of recession): for an extended-real-valued function
`f : ℝ^n → (-∞, +∞]`, a nonzero vector `y` is a direction of recession of `f` when for every
`x ∈ dom f` and every `λ ≥ 0`, one has `f (x + λ y) ≤ f x`; equivalently, the function
`λ ↦ f (x + λ y)` is non-increasing on `[0, ∞)`. -/
def IsDirectionOfRecessionWithTop {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ)
    (y : Fin n → ℝ) : Prop :=
  y ≠ 0 ∧ ∀ x ∈ effectiveDomainWithTop f, ∀ t : ℝ, 0 ≤ t → f (x + t • y) ≤ f x

/-- Definition 6.27.5 (Parabolic convex set): the set `P ⊆ ℝ²` is
`{(ξ₁, ξ₂) ∈ ℝ² | ξ₂ ≥ ξ₁²}`. -/
def parabolicConvexSet : Set (ℝ × ℝ) :=
  {ξ | ξ.2 ≥ ξ.1 ^ (2 : ℕ)}

/-- A concrete Euclidean model of `ℝ²`. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- Definition 6.27.7 (Squared distance function): for a set `P ⊆ ℝ²` and each `x ∈ ℝ²`, define
`f₀(x)` to be the infimum of the squared Euclidean distances `‖x - y‖²` as `y` ranges over `P`.
Here the infimum is taken in `WithTop ℝ`, so `squaredDistance P x` takes values in `[0, +∞]`;
in particular, this convention gives `squaredDistance P x = ⊤` when `P = ∅`. -/
noncomputable def squaredDistance (P : Set EuclideanPlane) (x : EuclideanPlane) : WithTop ℝ :=
  sInf ((fun y : EuclideanPlane => ((‖x - y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) '' P)

/-- The parabolic convex set viewed inside the Euclidean-space model of `ℝ²`. -/
def parabolicConvexSetEuclidean : Set EuclideanPlane :=
  {ξ | ξ (1 : Fin 2) ≥ ξ (0 : Fin 2) ^ (2 : ℕ)}

/-- The squared-distance function specialized to the parabolic convex set. -/
noncomputable def squaredDistanceToParabolicConvexSet : EuclideanPlane → WithTop ℝ :=
  fun x => squaredDistance parabolicConvexSetEuclidean x

/-- Definition 6.27.6 (Indicator function): for a set `C ⊆ ℝ^n`, the indicator function
`δ(· | C)` is the extended-real-valued function equal to `0` on `C` and `+∞` outside `C`.
This reuses the existing `EReal`-valued indicator function already defined in the project. -/
noncomputable abbrev indicatorFunctionEReal {n : ℕ} (C : Set (Fin n → ℝ)) :
    (Fin n → ℝ) → EReal :=
  indicatorFunction C

/-- The auxiliary function `f₁` on the Euclidean plane is the squared norm `x ↦ ‖x‖²`,
viewed as a `(-∞, +∞]`-valued function with no `+∞` values. -/
noncomputable def parabolicNormSquareFunction : EuclideanPlane → WithTop ℝ :=
  fun x => ((‖x‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)

/-- The auxiliary function `f₂` on the Euclidean plane is the indicator `δ(· | P)` of the
parabolic convex set `P`, taking the value `0` on `P` and `+∞` outside `P`. -/
noncomputable def parabolicIndicatorFunction : EuclideanPlane → WithTop ℝ :=
  fun x => @ite _ (x ∈ parabolicConvexSetEuclidean)
    ((Classical.decPred fun y : EuclideanPlane => y ∈ parabolicConvexSetEuclidean) x)
    (0 : WithTop ℝ) ⊤

/-- Definition 6.27.8 (Auxiliary functions; The function `f`): define the three functions
`(f₁, f₂, f)` on `ℝ²` by `f₁(x) = ‖x‖²`, `f₂(x) = δ(x | P)`, and, for
`x = (ξ₁, ξ₂) ∈ ℝ²`, `f(x) = f₀(ξ₁, ξ₂) - ξ₁`, where `f₀` is the squared-distance function to
the parabolic set `P`. In Lean, `ξ₁` is the first coordinate `x (0 : Fin 2)`. -/
noncomputable def parabolicAuxiliaryAndObjectiveFunctions :
    (EuclideanPlane → WithTop ℝ) ×
      ((EuclideanPlane → WithTop ℝ) × (EuclideanPlane → WithTop ℝ)) :=
  (parabolicNormSquareFunction, (parabolicIndicatorFunction,
    fun x => squaredDistanceToParabolicConvexSet x - (x (0 : Fin 2) : ℝ)))

/-- The parabolic objective function `f` is the third component of the bundled triple
`(f₁, f₂, f)`. -/
noncomputable def parabolicObjectiveFunction : EuclideanPlane → WithTop ℝ :=
  parabolicAuxiliaryAndObjectiveFunctions.2.2

-- Proof sketch: the squared-distance function to a nonempty closed convex set is finite and
-- convex, and subtracting the linear coordinate map `x ↦ x₁` preserves both properties.
/-- Helper for Proposition 6.27.8: the Euclidean parabolic set contains the origin, so the
squared-distance infimum is taken over a nonempty set. -/
lemma helperForProposition_6_27_8_parabolicConvexSetEuclidean_nonempty :
    parabolicConvexSetEuclidean.Nonempty := by
  -- The origin satisfies the defining inequality `0 ≥ 0²`.
  refine ⟨0, ?_⟩
  simp [parabolicConvexSetEuclidean]

/-- Helper for Proposition 6.27.8: the Euclidean parabolic set is convex. -/
lemma helperForProposition_6_27_8_parabolicConvexSetEuclidean_convex :
    Convex ℝ parabolicConvexSetEuclidean := by
  intro x hx y hy a b ha hb hab
  -- Unpack membership in the parabolic set into the two scalar inequalities on coordinates.
  dsimp [parabolicConvexSetEuclidean] at hx hy
  -- Rewrite the goal coordinatewise to isolate the scalar inequality on the parabola.
  change a * x (1 : Fin 2) + b * y (1 : Fin 2) ≥
    (a * x (0 : Fin 2) + b * y (0 : Fin 2)) ^ (2 : ℕ)
  -- The square function is convex, so the square of the convex combination stays below
  -- the convex combination of the squares.
  have hsquare :
      (a * x (0 : Fin 2) + b * y (0 : Fin 2)) ^ (2 : ℕ) ≤
        a * (x (0 : Fin 2)) ^ (2 : ℕ) + b * (y (0 : Fin 2)) ^ (2 : ℕ) := by
    have hab_nonneg :
        0 ≤ a * b * (x (0 : Fin 2) - y (0 : Fin 2)) ^ (2 : ℕ) := by
      positivity
    nlinarith [hab, hab_nonneg]
  -- Then use the hypotheses defining membership in the parabolic region.
  have hcoords :
      a * (x (0 : Fin 2)) ^ (2 : ℕ) + b * (y (0 : Fin 2)) ^ (2 : ℕ) ≤
        a * x (1 : Fin 2) + b * y (1 : Fin 2) := by
    nlinarith [hx, hy, ha, hb]
  linarith

/-- Helper for Proposition 6.27.8: the squared-distance function is the coercion of the real
infimum of squared norms over the parabolic set. -/
lemma helperForProposition_6_27_8_squaredDistanceToParabolicConvexSet_eq_coe_sInf
    (x : EuclideanPlane) :
    squaredDistanceToParabolicConvexSet x =
      ((sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) ''
        parabolicConvexSetEuclidean) : ℝ) : WithTop ℝ) := by
  let S : Set ℝ := ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) '' parabolicConvexSetEuclidean)
  have hS_nonempty : S.Nonempty := by
    -- Evaluate the objective at the origin to produce one element of the image set.
    rcases helperForProposition_6_27_8_parabolicConvexSetEuclidean_nonempty with ⟨y, hy⟩
    exact ⟨‖x - y‖ ^ (2 : ℕ), ⟨y, hy, rfl⟩⟩
  have hS_bddBelow : BddBelow S := by
    -- Every squared norm is nonnegative, so `0` is a lower bound.
    refine ⟨0, ?_⟩
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact pow_nonneg (norm_nonneg (x - y)) 2
  have hsInf :
      ((sInf S : ℝ) : WithTop ℝ) =
        sInf ((fun z : ℝ => (z : WithTop ℝ)) '' S) := by
    simpa using (WithTop.coe_sInf' (s := S) hS_nonempty hS_bddBelow)
  -- Rewrite the `WithTop`-valued infimum as the coercion of the corresponding real infimum.
  calc
    squaredDistanceToParabolicConvexSet x
        = sInf ((fun z : ℝ => (z : WithTop ℝ)) '' S) := by
            simp [squaredDistanceToParabolicConvexSet, squaredDistance, S, Set.image_image]
    _ = ((sInf S : ℝ) : WithTop ℝ) := hsInf.symm

/-- Helper for Proposition 6.27.8: the parabolic objective is the coercion of the real
squared-distance envelope minus the first coordinate. -/
lemma helperForProposition_6_27_8_parabolicObjectiveFunction_eq_coe_realEnvelope
    (x : EuclideanPlane) :
    parabolicObjectiveFunction x =
      (((sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) ''
        parabolicConvexSetEuclidean) : ℝ) - x (0 : Fin 2) : ℝ) : WithTop ℝ) := by
  -- Unfold the bundled definition to expose the scalar subtraction formula for `f`.
  change squaredDistanceToParabolicConvexSet x - (x (0 : Fin 2) : ℝ) =
    (((sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) ''
      parabolicConvexSetEuclidean) : ℝ) - x (0 : Fin 2) : ℝ) : WithTop ℝ)
  -- First rewrite the squared-distance term into a genuine real infimum.
  rw [helperForProposition_6_27_8_squaredDistanceToParabolicConvexSet_eq_coe_sInf]
  -- Subtracting a real from a finite `WithTop` value stays inside the real copy.
  simp

/-- Helper for Proposition 6.27.8: the real squared-distance envelope over the parabolic set is
convex on the whole Euclidean plane. -/
lemma helperForProposition_6_27_8_realEnvelope_convex :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanPlane =>
        sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) ''
          parabolicConvexSetEuclidean)) := by
  have hconv_rpow :
      ConvexOn ℝ Set.univ
        (fun x : EuclideanPlane =>
          sInf ((fun y : EuclideanPlane => Real.rpow (dist x y) (2 : ℝ)) ''
            parabolicConvexSetEuclidean)) := by
    -- Reuse the chapter-26 theorem for distance-power envelopes over nonempty convex sets.
    simpa using
      (helperForText_26_3_3_1_convex_infDist_rpow
        (C := parabolicConvexSetEuclidean)
        helperForProposition_6_27_8_parabolicConvexSetEuclidean_nonempty
        helperForProposition_6_27_8_parabolicConvexSetEuclidean_convex
        (by norm_num : (1 : ℝ) < 2))
  -- Specialize `p = 2` and rewrite `dist` as the norm of the difference.
  simpa [dist_eq_norm, Real.rpow_natCast] using hconv_rpow

/-- Helper for Proposition 6.27.8: the negative first-coordinate map is affine, hence convex on
the whole Euclidean plane. -/
lemma helperForProposition_6_27_8_negFirstCoordinate_convex :
    ConvexOn ℝ Set.univ (fun x : EuclideanPlane => -(x (0 : Fin 2))) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The coordinate projection preserves affine combinations exactly.
  simp [smul_eq_mul]

/-- Proposition 6.27.8: the function `f` defined by
`f(x) = f₀(x) - ξ₁` for `x = (ξ₁, ξ₂) ∈ ℝ²`, where `f₀` is the squared-distance function to the
parabolic convex set, is finite everywhere on `ℝ²` and is convex. -/
theorem parabolicObjectiveFunction_finite_and_convex :
    (∀ x : EuclideanPlane, parabolicObjectiveFunction x < (⊤ : WithTop ℝ)) ∧
      Convex ℝ {p : EuclideanPlane × ℝ | parabolicObjectiveFunction p.1 ≤ (p.2 : WithTop ℝ)} :=
    by
  let g : EuclideanPlane → ℝ := fun x =>
    sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) '' parabolicConvexSetEuclidean) -
      x (0 : Fin 2)
  have hEnvelopeConvex :
      ConvexOn ℝ Set.univ
        (fun x : EuclideanPlane =>
          sInf ((fun y : EuclideanPlane => ‖x - y‖ ^ (2 : ℕ)) ''
            parabolicConvexSetEuclidean)) :=
    helperForProposition_6_27_8_realEnvelope_convex
  have hLinearConvex :
      ConvexOn ℝ Set.univ (fun x : EuclideanPlane => -(x (0 : Fin 2))) :=
    helperForProposition_6_27_8_negFirstCoordinate_convex
  have hg_convex : ConvexOn ℝ Set.univ g := by
    -- The objective is the sum of the convex distance envelope and the convex linear term.
    simpa [g, sub_eq_add_neg] using hEnvelopeConvex.add hLinearConvex
  constructor
  · intro x
    -- Rewriting the objective as a coerced real immediately gives finiteness.
    rw [helperForProposition_6_27_8_parabolicObjectiveFunction_eq_coe_realEnvelope]
    exact WithTop.coe_lt_top _
  · intro p hp q hq a b ha hb hab
    -- Translate both epigraph hypotheses into real inequalities for `g`.
    have hp_coe : (((g p.1 : ℝ)) : WithTop ℝ) ≤ (p.2 : WithTop ℝ) := by
      simpa [g, helperForProposition_6_27_8_parabolicObjectiveFunction_eq_coe_realEnvelope] using hp
    have hq_coe : (((g q.1 : ℝ)) : WithTop ℝ) ≤ (q.2 : WithTop ℝ) := by
      simpa [g, helperForProposition_6_27_8_parabolicObjectiveFunction_eq_coe_realEnvelope] using hq
    have hp_real : g p.1 ≤ p.2 := WithTop.coe_le_coe.mp hp_coe
    have hq_real : g q.1 ≤ q.2 := WithTop.coe_le_coe.mp hq_coe
    have hg_mix :
        g (a • p.1 + b • q.1) ≤ a * g p.1 + b * g q.1 :=
      hg_convex.2 (by simp) (by simp) ha hb hab
    have hupper :
        a * g p.1 + b * g q.1 ≤ a * p.2 + b * q.2 := by
      nlinarith [hp_real, hq_real, ha, hb]
    -- The mixed point stays in the epigraph because the second coordinate dominates `g`.
    change parabolicObjectiveFunction (a • p.1 + b • q.1) ≤
      (((a : ℝ) * p.2 + (b : ℝ) * q.2 : ℝ) : WithTop ℝ)
    rw [helperForProposition_6_27_8_parabolicObjectiveFunction_eq_coe_realEnvelope]
    change (((g (a • p.1 + b • q.1) : ℝ)) : WithTop ℝ) ≤
      (((a : ℝ) * p.2 + (b : ℝ) * q.2 : ℝ) : WithTop ℝ)
    exact WithTop.coe_le_coe.mpr (le_trans hg_mix hupper)

-- Proof sketch: if `x` lies in some real sublevel set, then `f x ≤ α < ⊤`, so `f x` is finite;
-- conversely, if `f x < ⊤`, choose a real number `α` strictly above the finite value `f x`.
/-- Helper for Proposition 6.27.3: membership in a real sublevel set already forces the
function value to be finite. -/
lemma helperForProposition_6_27_3_mem_effectiveDomain_of_mem_sublevel {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} {α : ℝ} :
    x ∈ sublevelSet f α → x ∈ effectiveDomainWithTop f := by
  intro hx
  -- Compare the finite upper bound `α` with `⊤` to show that `f x` cannot be infinite.
  change f x < (⊤ : WithTop ℝ)
  exact lt_of_le_of_lt hx (WithTop.coe_lt_top α)

/-- Helper for Proposition 6.27.3: a finite `WithTop ℝ` value comes from an actual real level,
so the point lies in some real sublevel set. -/
lemma helperForProposition_6_27_3_exists_sublevel_of_mem_effectiveDomain {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} :
    x ∈ effectiveDomainWithTop f → ∃ α : ℝ, x ∈ sublevelSet f α := by
  intro hx
  -- Rewrite finiteness as `f x ≠ ⊤` so that `WithTop.ne_top_iff_exists` can recover a real value.
  rw [show effectiveDomainWithTop f = {y | f y ≠ (⊤ : WithTop ℝ)} by
    ext y
    simp [effectiveDomainWithTop, lt_top_iff_ne_top]] at hx
  rcases (WithTop.ne_top_iff_exists.mp hx) with ⟨α, hα⟩
  -- Use the recovered real value itself as the desired sublevel index.
  use α
  change f x ≤ (α : WithTop ℝ)
  rw [← hα]

/-- Helper for Proposition 6.27.3: a point belongs to the union of all real sublevel sets
exactly when the function is finite there. -/
lemma helperForProposition_6_27_3_mem_iUnion_sublevelSet_iff {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} :
    x ∈ (⋃ α : ℝ, sublevelSet f α) ↔ x ∈ effectiveDomainWithTop f := by
  constructor
  · intro hx
    -- Unpack the union membership into a concrete real sublevel witness.
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨α, hα⟩
    exact helperForProposition_6_27_3_mem_effectiveDomain_of_mem_sublevel hα
  · intro hx
    -- Recover a real level containing `x` and then repackage it as union membership.
    rw [Set.mem_iUnion]
    exact helperForProposition_6_27_3_exists_sublevel_of_mem_effectiveDomain hx

/-- Proposition 6.27.3 (Union of sublevel sets): for a proper function
`f : ℝ^n → (-∞, +∞]`, the union of all real sublevel sets is the effective domain
`dom f = {x ∈ ℝ^n | f x < +∞}`. -/
theorem iUnion_sublevelSet_eq_effectiveDomainWithTop {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hproper : Set.Nonempty (effectiveDomainWithTop f)) :
    (⋃ α : ℝ, sublevelSet f α) = effectiveDomainWithTop f := by
  let _ := hproper
  -- Prove equality by checking pointwise membership on both sides.
  ext x
  -- The helper packages the two directions: bounded above by a real level versus finiteness.
  exact helperForProposition_6_27_3_mem_iUnion_sublevelSet_iff

-- Proof sketch: if `x` and `y` lie in the minimum set, then both satisfy
-- `f x = inf f` and `f y = inf f`; convexity of `f` gives
-- `f ((1 - t) • x + t • y) ≤ inf f`, while `inf f` is a lower bound for all values of `f`,
-- hence equality holds and every convex combination still lies in the minimum set.
/-- Helper for Proposition 6.27.4: if the function infimum is `-∞`, then no point can realize
that value because `f` only takes values in `(-∞, +∞]`. -/
lemma helperForProposition_6_27_4_minimumSet_eq_empty_of_functionInfimum_eq_bot {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ}
    (h : functionInfimum f = (⊥ : WithBot (WithTop ℝ))) :
    minimumSet f = (∅ : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    -- Rewrite membership using the `⊥` infimum; the simplifier reduces this to a contradiction.
    simp [minimumSet, h] at hx
  · intro hx
    -- The reverse implication is vacuous because `x ∈ ∅` is impossible.
    simp at hx

/-- Helper for Proposition 6.27.4: if the function infimum is `+∞`, then every value of `f`
must be `+∞`, so every point is a minimizer. -/
lemma helperForProposition_6_27_4_minimumSet_eq_univ_of_functionInfimum_eq_top {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ}
    (h : functionInfimum f = (⊤ : WithBot (WithTop ℝ))) :
    minimumSet f = (Set.univ : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro _
    -- Membership in `univ` is automatic.
    simp
  · intro _
    -- The infimum is always a lower bound on the range of `f`.
    have hlower : functionInfimum f ≤ ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      exact sInf_le (Set.mem_range.mpr ⟨x, rfl⟩)
    -- After rewriting the infimum as `⊤`, the lower-bound inequality forces `f x = ⊤`.
    have htop : (((f x : WithTop ℝ) : WithBot (WithTop ℝ)) = ⊤) := by
      exact top_le_iff.mp (by simpa [h] using hlower)
    have hfx_top : f x = (⊤ : WithTop ℝ) := by
      exact WithBot.coe_eq_top.mp htop
    -- Repackage the pointwise equality as membership in the minimum set.
    simp [minimumSet, h, hfx_top]

/-- Helper for Proposition 6.27.4: if the function infimum is neither `-∞` nor `+∞`, then it
is represented by a finite real number. -/
lemma helperForProposition_6_27_4_exists_real_of_functionInfimum_ne_bot_ne_top {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ}
    (hne_bot : functionInfimum f ≠ (⊥ : WithBot (WithTop ℝ)))
    (hne_top : functionInfimum f ≠ (⊤ : WithBot (WithTop ℝ))) :
    ∃ α : ℝ, functionInfimum f = (((α : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
  -- First remove the outer `WithBot`, then remove the inner `WithTop`.
  rcases WithBot.ne_bot_iff_exists.mp hne_bot with ⟨a, ha⟩
  have ha_ne_top : a ≠ (⊤ : WithTop ℝ) := by
    intro ha_top
    apply hne_top
    rw [← ha, ha_top]
    exact WithBot.coe_eq_top.mpr rfl
  rcases WithTop.ne_top_iff_exists.mp ha_ne_top with ⟨α, hα⟩
  -- The recovered real number `α` is exactly the finite value of the infimum.
  refine ⟨α, ?_⟩
  rw [← ha, ← hα]

/-- Helper for Proposition 6.27.4: once the infimum is a finite real value `α`, the minimum set
coincides with the `α`-sublevel set. -/
lemma helperForProposition_6_27_4_minimumSet_eq_sublevelSet_of_functionInfimum_eq_real {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {α : ℝ}
    (h : functionInfimum f = (((α : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ))) :
    minimumSet f = sublevelSet f α := by
  ext x
  constructor
  · intro hx
    -- A minimizer has value exactly equal to the finite infimum, hence lies in the sublevel set.
    have hfx : (f x : WithTop ℝ) = (α : WithTop ℝ) := by
      exact WithBot.coe_eq_coe.mp (by simpa [minimumSet, h] using hx)
    rw [sublevelSet, Set.mem_setOf_eq, hfx]
  · intro hx
    -- Membership in the sublevel set gives the upper bound `f x ≤ α = inf f`.
    have hupper : ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) ≤ functionInfimum f := by
      simpa [sublevelSet, h] using hx
    -- The infimum is also a lower bound for every pointwise value in the range.
    have hlower : functionInfimum f ≤ ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      exact sInf_le (Set.mem_range.mpr ⟨x, rfl⟩)
    -- Combining the two inequalities identifies `f x` with the infimum.
    exact le_antisymm hupper hlower

/-- Proposition 6.27.4 (Convexity of the minimum set): if
`f : ℝ^n → (-∞, +∞]` is a convex function and `M` is its minimum set,
then `M` is a convex subset of `ℝ^n`. -/
theorem convex_minimumSet {n : ℕ} {f : (Fin n → ℝ) → WithTop ℝ}
    (hf : IsConvexFunction f) :
    Convex ℝ (minimumSet f) := by
  -- Split according to whether the infimum is `-∞`, `+∞`, or a finite real number.
  by_cases hbot : functionInfimum f = (⊥ : WithBot (WithTop ℝ))
  · -- In the `-∞` case the minimum set is empty, hence convex.
    rw [helperForProposition_6_27_4_minimumSet_eq_empty_of_functionInfimum_eq_bot hbot]
    exact convex_empty
  · by_cases htop : functionInfimum f = (⊤ : WithBot (WithTop ℝ))
    · -- In the `+∞` case the minimum set is all of space, hence convex.
      rw [helperForProposition_6_27_4_minimumSet_eq_univ_of_functionInfimum_eq_top htop]
      exact convex_univ
    · -- Otherwise the infimum is finite, so the minimum set is a real sublevel set.
      rcases helperForProposition_6_27_4_exists_real_of_functionInfimum_ne_bot_ne_top hbot htop with
        ⟨α, hα⟩
      rw [helperForProposition_6_27_4_minimumSet_eq_sublevelSet_of_functionInfimum_eq_real hα]
      exact convex_sublevelSet hf α

-- Proof sketch: the minimum set is the set where `f` attains its infimum; for a closed convex
-- function, lower semicontinuity forces the set of minimizers to be closed.
/-- Proposition 6.27.5 (Closedness of the minimum set): if
`f : ℝ^n → (-∞, +∞]` is a closed convex function and `M` is its minimum set,
then `M` is a closed subset of `ℝ^n`. -/
theorem isClosed_minimumSet_of_closed_convexFunction {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf_closed : LowerSemicontinuous f)
    (hf_convex : IsConvexFunction f) :
    IsClosed (minimumSet f) := by
  -- Split according to whether the infimum is `-∞`, `+∞`, or a finite real number.
  by_cases hbot : functionInfimum f = (⊥ : WithBot (WithTop ℝ))
  · -- In the `-∞` case the minimum set is empty, and the empty set is closed.
    rw [helperForProposition_6_27_4_minimumSet_eq_empty_of_functionInfimum_eq_bot hbot]
    exact isClosed_empty
  · by_cases htop : functionInfimum f = (⊤ : WithBot (WithTop ℝ))
    · -- In the `+∞` case the minimum set is all of space, and the whole space is closed.
      rw [helperForProposition_6_27_4_minimumSet_eq_univ_of_functionInfimum_eq_top htop]
      exact isClosed_univ
    · -- Otherwise the infimum is a finite real number, so the minimum set is a real sublevel set.
      rcases helperForProposition_6_27_4_exists_real_of_functionInfimum_ne_bot_ne_top hbot htop with
        ⟨α, hα⟩
      -- Rewrite the minimum set using the finite infimum and then invoke closedness of sublevel sets.
      rw [helperForProposition_6_27_4_minimumSet_eq_sublevelSet_of_functionInfimum_eq_real hα]
      exact isClosed_sublevelSet_of_closed_convexFunction hf_closed hf_convex α

-- Proof sketch: use the subgradient inequality specialized to the zero functional to show that
-- `0 ∈ ∂f(x)` forces `f z ≥ f x` for every `z`, hence `x` is a minimizer; conversely, if `x`
-- minimizes `f`, then the same inequality with zero right-hand side shows that the zero
-- functional is a subgradient at `x`.
/-- Helper for Proposition 6.27.6: the function infimum lies below every point value in the
range used to define it. -/
lemma helperForProposition_6_27_6_functionInfimum_le_pointValue {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (z : Fin n → ℝ) :
    functionInfimum f ≤ ((f z : WithTop ℝ) : WithBot (WithTop ℝ)) := by
  -- The value `f z` is one of the elements appearing in the range whose infimum defines
  -- `functionInfimum f`.
  unfold functionInfimum
  exact sInf_le (Set.mem_range.mpr ⟨z, rfl⟩)

/-- Helper for Proposition 6.27.6: belonging to the minimum set means that the value at `x`
is below every point value of `f`. -/
lemma helperForProposition_6_27_6_mem_minimumSet_iff_pointwiseLowerBound {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} :
    x ∈ minimumSet f ↔
      ∀ z, ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) ≤
        ((f z : WithTop ℝ) : WithBot (WithTop ℝ)) := by
  constructor
  · intro hx z
    -- First rewrite minimum-set membership as the equality `f x = inf f`.
    have hx_eq : ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) = functionInfimum f := by
      simpa [minimumSet] using hx
    -- Then transport the universal lower bound of the infimum to the value at `x`.
    have hz : functionInfimum f ≤ ((f z : WithTop ℝ) : WithBot (WithTop ℝ)) :=
      helperForProposition_6_27_6_functionInfimum_le_pointValue f z
    simpa [hx_eq] using hz
  · intro hx
    -- Show that the value at `x` is itself a lower bound for the full range of `f`.
    have hxle : ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) ≤ functionInfimum f := by
      unfold functionInfimum
      exact le_sInf (by
        rintro _ ⟨z, rfl⟩
        exact hx z)
    -- The defining infimum is always below the particular value attained at `x`.
    have hle : functionInfimum f ≤ ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) :=
      helperForProposition_6_27_6_functionInfimum_le_pointValue f x
    -- The two opposite inequalities recover the defining equality of `minimumSet f`.
    simp [minimumSet, le_antisymm hle hxle]

/-- Helper for Proposition 6.27.6: the `EReal` order for the lifted function is exactly the same
as the `WithBot (WithTop ℝ)` order on the original `WithTop ℝ` values. -/
lemma helperForProposition_6_27_6_withTopFunctionToEReal_order_iff {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x z : Fin n → ℝ} :
    withTopFunctionToEReal f x ≤ withTopFunctionToEReal f z ↔
      ((f x : WithTop ℝ) : WithBot (WithTop ℝ)) ≤
        ((f z : WithTop ℝ) : WithBot (WithTop ℝ)) := by
  -- This is only the definitional identification `EReal = WithBot (WithTop ℝ)`.
  rfl

/-- Helper for Proposition 6.27.6: the zero dual vector is a subgradient exactly when the lifted
function value at `x` is below every lifted function value. -/
lemma helperForProposition_6_27_6_zero_mem_subdifferentialAt_iff_pointwiseLowerBound {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} {x : Fin n → ℝ} :
    (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt (withTopFunctionToEReal f) x ↔
      ∀ z, withTopFunctionToEReal f x ≤ withTopFunctionToEReal f z := by
  -- Unfold subgradient membership and specialize the subgradient inequality to the zero
  -- functional, whose pairing term vanishes.
  simp [mem_subdifferentialAt_iff, IsSubgradientAt]

/-- Proposition 6.27.6 (Characterization of minimizers by the subdifferential): let
`f : ℝ^n → (-∞, +∞]` be a proper convex function, and let `M` be the minimum set of `f`.
Then for any `x ∈ ℝ^n`, one has `x ∈ M` if and only if the zero dual vector belongs to the
subdifferential of `f` at `x`. Equivalently, `x` is a minimizer exactly when `x^* = 0` is a
subgradient of `f` at `x`. -/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hproper : Set.Nonempty (effectiveDomainWithTop f))
    (hf : IsConvexFunction f) (x : Fin n → ℝ) :
    x ∈ minimumSet f ↔
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt (withTopFunctionToEReal f) x := by
  -- Keep the textbook hypotheses in scope even though this characterization is purely
  -- definitional and uses only the infimum and subgradient inequalities.
  have _ : Set.Nonempty (effectiveDomainWithTop f) := hproper
  have _ : IsConvexFunction f := hf
  -- Rewrite minimizer membership as the pointwise lower-bound condition in
  -- `WithBot (WithTop ℝ)`.
  rw [helperForProposition_6_27_6_mem_minimumSet_iff_pointwiseLowerBound]
  -- Rewrite zero-subgradient membership as the same lower-bound condition in `EReal`.
  rw [helperForProposition_6_27_6_zero_mem_subdifferentialAt_iff_pointwiseLowerBound]
  constructor
  · intro hx z
    -- Convert the lifted `EReal` inequality back to the original infimum-order formulation.
    exact (helperForProposition_6_27_6_withTopFunctionToEReal_order_iff
      (f := f) (x := x) (z := z)).2 (hx z)
  · intro hx z
    -- Convert the minimum-set lower bound into the lifted `EReal` inequality used by
    -- subgradients.
    exact (helperForProposition_6_27_6_withTopFunctionToEReal_order_iff
      (f := f) (x := x) (z := z)).1 (hx z)

-- Proof sketch: for a convex function, the restriction of `f` to any line segment is convex in
-- one variable. If some `y` satisfied `f y < f x`, then points on the segment from `x` to `y`
-- sufficiently close to `x` would also satisfy `f z < f x`, contradicting local minimality.
-- The resulting global minimality then yields `0 ∈ ∂f(x)` from Proposition 6.27.6.
/-- Helper for Proposition 6.27.7: convexity of the epigraph bounds the function value at a
segment point by the affine combination of the two finite endpoint heights. -/
lemma helperForProposition_6_27_7_value_le_affineCombinationOfHeights {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf : IsConvexFunction f)
    {x y : Fin n → ℝ} {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : f x ≤ (a : WithTop ℝ)) (hy : f y ≤ (b : WithTop ℝ)) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : WithTop ℝ) := by
  -- Repackage convexity of `f` as convexity of its epigraph.
  have h_epigraph : Convex ℝ (epigraphWithTop f) :=
    helperForProposition_6_27_1_convex_epigraphWithTop_of_IsConvexFunction hf
  have hx_epigraph : (x, a) ∈ epigraphWithTop f := hx
  have hy_epigraph : (y, b) ∈ epigraphWithTop f := hy
  -- Apply epigraph convexity to the affine combination with weights `1 - t` and `t`.
  have h_combo : (1 - t) • (x, a) + t • (y, b) ∈ epigraphWithTop f :=
    h_epigraph hx_epigraph hy_epigraph (by nlinarith [ht1]) ht0 (by nlinarith)
  -- Read the product-space conclusion as the desired scalar inequality.
  simpa [epigraphWithTop, smul_eq_mul] using h_combo

/-- Helper for Proposition 6.27.7: the standard short segment point from `x` toward `y`
stays inside the local-minimum ball. -/
lemma helperForProposition_6_27_7_segmentPoint_mem_ball {n : ℕ}
    {x y : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε) :
    let t : ℝ := ε / (2 * (ε + ‖y - x‖))
    let z : Fin n → ℝ := (1 - t) • x + t • y
    0 < t ∧ t < 1 ∧ ‖z - x‖ < ε := by
  let t : ℝ := ε / (2 * (ε + ‖y - x‖))
  let z : Fin n → ℝ := (1 - t) • x + t • y
  have hnorm_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg (y - x)
  have hden_pos : 0 < 2 * (ε + ‖y - x‖) := by
    nlinarith
  have ht_pos : 0 < t := by
    -- Positivity comes directly from the explicit formula for `t`.
    dsimp [t]
    exact div_pos hε hden_pos
  have ht_lt_one : t < 1 := by
    -- The denominator is strictly larger than the numerator.
    dsimp [t]
    refine (div_lt_iff₀ hden_pos).2 ?_
    nlinarith
  have hz_sub : z - x = t • (y - x) := by
    -- Along the segment, the displacement from `x` is exactly `t (y - x)`.
    ext i
    dsimp [z, t]
    ring
  have hdist : ‖z - x‖ < ε := by
    -- Rewrite the distance using the previous displacement identity and simplify the norm.
    have hnorm : ‖z - x‖ = t * ‖y - x‖ := by
      calc
        ‖z - x‖ = ‖t • (y - x)‖ := by rw [hz_sub]
        _ = ‖t‖ * ‖y - x‖ := norm_smul t (y - x)
        _ = t * ‖y - x‖ := by simp [Real.norm_eq_abs, abs_of_pos ht_pos]
    rw [hnorm]
    dsimp [t]
    have hnum : ε * ‖y - x‖ < ε * (2 * (ε + ‖y - x‖)) := by
      nlinarith
    have hdiv : ε * ‖y - x‖ / (2 * (ε + ‖y - x‖)) < ε := by
      exact (div_lt_iff₀ hden_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hnum)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  exact ⟨ht_pos, ht_lt_one, hdist⟩

/-- Helper for Proposition 6.27.7: a finite local minimum of a convex function is already a
global lower bound. -/
lemma helperForProposition_6_27_7_globalLowerBound_of_localMinimum {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hf : IsConvexFunction f)
    {x : Fin n → ℝ} (hx : x ∈ effectiveDomainWithTop f)
    (hlocal : ∃ ε : ℝ, ε > 0 ∧ ∀ z : Fin n → ℝ, ‖z - x‖ < ε → f z ≥ f x) :
    ∀ y : Fin n → ℝ, f y ≥ f x := by
  intro y
  by_contra hy_not_ge
  have hy_lt : f y < f x := lt_of_not_ge hy_not_ge
  rcases hlocal with ⟨ε, hε, hlocalε⟩
  have hx_ne_top : f x ≠ (⊤ : WithTop ℝ) := (lt_top_iff_ne_top.mp hx)
  rcases WithTop.ne_top_iff_exists.mp hx_ne_top with ⟨a, ha⟩
  have hy_lt_top : f y < (⊤ : WithTop ℝ) := lt_trans hy_lt hx
  have hy_ne_top : f y ≠ (⊤ : WithTop ℝ) := (lt_top_iff_ne_top.mp hy_lt_top)
  rcases WithTop.ne_top_iff_exists.mp hy_ne_top with ⟨b, hb⟩
  have hb_lt_ha : b < a := by
    have hb_lt_ha_top : (b : WithTop ℝ) < (a : WithTop ℝ) := by
      calc
        (b : WithTop ℝ) = f y := hb
        _ < f x := hy_lt
        _ = (a : WithTop ℝ) := ha.symm
    exact_mod_cast hb_lt_ha_top
  let t : ℝ := ε / (2 * (ε + ‖y - x‖))
  let z : Fin n → ℝ := (1 - t) • x + t • y
  have hsegment : 0 < t ∧ t < 1 ∧ ‖z - x‖ < ε := by
    -- Choose the explicit nearby point on the segment from `x` to `y`.
    simpa [t, z] using
      (helperForProposition_6_27_7_segmentPoint_mem_ball (x := x) (y := y) (ε := ε) hε)
  rcases hsegment with ⟨ht_pos, ht_lt_one, hz_mem_ball⟩
  have hz_le : f z ≤ (((1 - t) * a + t * b : ℝ) : WithTop ℝ) := by
    -- Convexity controls the function value at `z` by the interpolated endpoint heights.
    apply helperForProposition_6_27_7_value_le_affineCombinationOfHeights hf ht_pos.le ht_lt_one.le
    · simpa [ha]
    · simpa [hb]
  have hstrict_combo : (((1 - t) * a + t * b : ℝ) : WithTop ℝ) < f x := by
    -- Because `b < a` and `t > 0`, the convex combination of the heights is strictly below `a`.
    have hreal : (1 - t) * a + t * b < a := by
      nlinarith
    have hreal_top : (((1 - t) * a + t * b : ℝ) : WithTop ℝ) < (a : WithTop ℝ) := by
      exact_mod_cast hreal
    simpa [ha] using hreal_top
  have hz_lt_fx : f z < f x := lt_of_le_of_lt hz_le hstrict_combo
  have hz_ge_fx : f z ≥ f x := hlocalε z hz_mem_ball
  exact (not_le_of_gt hz_lt_fx) hz_ge_fx

/-- Proposition 6.27.7 (A local minimum of a convex function is global): let
`f : ℝ^n → (-∞, +∞]` be a proper convex function, and let `x ∈ dom f`. If `x` is a finite local
minimum point of `f`, meaning that there exists `ε > 0` such that `f z ≥ f x` whenever
`‖z - x‖ < ε`, then `x` is a global minimum point of `f`, so `f y ≥ f x` for every `y ∈ ℝ^n`.
Consequently, `0 ∈ ∂f(x)`. -/
theorem localMinimumPoint_globalMinimizer_of_proper_convexFunction {n : ℕ}
    {f : (Fin n → ℝ) → WithTop ℝ} (hproper : Set.Nonempty (effectiveDomainWithTop f))
    (hf : IsConvexFunction f) {x : Fin n → ℝ} (hx : x ∈ effectiveDomainWithTop f)
    (hlocal : ∃ ε : ℝ, ε > 0 ∧ ∀ z : Fin n → ℝ, ‖z - x‖ < ε → f z ≥ f x) :
    (∀ y : Fin n → ℝ, f y ≥ f x) ∧
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt (withTopFunctionToEReal f) x := by
  -- First upgrade local minimality to the global pointwise lower bound promised by the text.
  have hglobal : ∀ y : Fin n → ℝ, f y ≥ f x :=
    helperForProposition_6_27_7_globalLowerBound_of_localMinimum hf hx hlocal
  constructor
  · exact hglobal
  · have hx_min : x ∈ minimumSet f := by
      -- Repackage the pointwise lower bound as membership in the minimum set.
      rw [helperForProposition_6_27_6_mem_minimumSet_iff_pointwiseLowerBound]
      intro z
      exact_mod_cast (hglobal z)
    -- Then invoke the previous minimizer/subdifferential characterization.
    exact (mem_minimumSet_iff_zero_mem_subdifferentialAt hproper hf x).mp hx_min

end Section27
end Chap06
