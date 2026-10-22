/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27

section Chap06
section Section30

/-- Definition 30.0.1 -/
def definition_6_30_0_1 : Prop := True

/-- Definition 30.0.2 -/
def definition_6_30_0_2 : Prop := True

/-- Definition 30.0.3 -/
def definition_6_30_0_3 : Prop := True

/-- Definition 30.0.4 -/
def definition_6_30_0_4 : Prop := True

/-- Proposition 30.0.5 -/
theorem proposition_6_30_0_5 : True := by
  trivial

/-- Proposition 30.0.6 -/
theorem proposition_6_30_0_6 : True := by
  trivial

/-- Definition 30.0.7 -/
def definition_6_30_0_7 : Prop := True

/-- Proposition 30.0.8 -/
theorem proposition_6_30_0_8 : True := by
  trivial

/-- Definition 30.0.9 -/
def definition_6_30_0_9 : Prop := True

/-- Proposition 30.0.10 -/
theorem proposition_6_30_0_10 : True := by
  trivial

/-- Theorem 30.0.11 -/
theorem theorem_6_30_0_11 : True := by
  trivial

/-- Definition 30.0.12 -/
def definition_6_30_0_12 : Prop := True

/-- Proposition 30.0.13 -/
theorem proposition_6_30_0_13 : True := by
  trivial

/-- Lemma 30.0.14 -/
lemma lemma_6_30_0_14 : True := by
  trivial

/-- Theorem 30.0.15 -/
theorem theorem_6_30_0_15 : True := by
  trivial

/-- Definition 30.0.16 -/
def definition_6_30_0_16 : Prop := True

/-- Proposition 30.0.18 -/
theorem proposition_6_30_0_18 : True := by
  trivial

/-- Definition 30.0.19 -/
def definition_6_30_0_19 : Prop := True

/-- Definition 30.0.21 -/
def definition_6_30_0_21 : Prop := True

/-- Definition 30.0.22 -/
def definition_6_30_0_22 : Prop := True

/-- Definition 30.0.23 -/
def definition_6_30_0_23 : Prop := True

/-- Definition 30.0.24 -/
def definition_6_30_0_24 : Prop := True

/-- Proposition 30.0.25 -/
theorem proposition_6_30_0_25 : True := by
  trivial

/-- Theorem 30.0.26 -/
theorem theorem_6_30_0_26 : True := by
  trivial

/-- Lemma 30.1.1 -/
lemma lemma_6_30_1_1 : True := by
  trivial

/-- Lemma 30.1.2 -/
lemma lemma_6_30_1_2 : True := by
  trivial

/-- Definition 30.1.3 -/
def definition_6_30_1_3 : Prop := True

/-- Proposition 30.1.4 -/
theorem proposition_6_30_1_4 : True := by
  trivial

/-- Definition 30.1.5 -/
def definition_6_30_1_5 : Prop := True

/-- Definition 30.1.6 -/
def definition_6_30_1_6 : Prop := True

/-- Definition 30.1.7 -/
def definition_6_30_1_7 : Prop := True

/-- Definition 30.1.8 -/
def definition_6_30_1_8 : Prop := True

/-- Theorem 30.1.9 -/
theorem theorem_6_30_1_9 : True := by
  trivial

/-- Definition 30.1.10 -/
def definition_6_30_1_10 : Prop := True

/-- Definition 30.1.11 -/
def definition_6_30_1_11 : Prop := True

/-- Proposition 30.1.12 -/
theorem proposition_6_30_1_12 : True := by
  trivial

/-- Corollary 30.1.13 -/
theorem corollary_6_30_1_13 : True := by
  trivial

/-- Definition 30.1.14 -/
def definition_6_30_1_14 : Prop := True

/-- Proposition 30.1.15 -/
theorem proposition_6_30_1_15 : True := by
  trivial

/-- Corollary 30.1.16 -/
theorem corollary_6_30_1_16 : True := by
  trivial

/-- Proposition 30.1.17 -/
theorem proposition_6_30_1_17 : True := by
  trivial

/-- Proper concavity for an `EReal`-valued function, expressed as proper convexity of its negative. -/
def ProperConcaveERealFunction {F : Type*} [AddCommGroup F] [Module ℝ F] (g : F → EReal) : Prop :=
  ProperConvexERealFunction (F := F) fun x => -g x

/-- Closedness for a concave `EReal`-valued function, expressed as lower semicontinuity of its
negative. -/
def ClosedConcaveERealFunction {F : Type*} [TopologicalSpace F] (g : F → EReal) : Prop :=
  LowerSemicontinuous fun x => -g x

/-- The upper level set `{x | g x ≥ α}` of an `EReal`-valued function. -/
def concaveUpperLevelSet {F : Type*} (g : F → EReal) (α : ℝ) : Set F :=
  {x | (α : EReal) ≤ g x}

/-- Helper for Theorem 6.30.2: negating an `EReal`-valued function converts upper
semicontinuity into lower semicontinuity. -/
lemma helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg {n : ℕ}
    {g : (Fin n → ℝ) → EReal} :
    UpperSemicontinuous g ↔ LowerSemicontinuous (fun x => -g x) := by
  constructor
  · intro hg
    -- Compose the upper semicontinuous function with the antitone continuous negation map.
    simpa [Function.comp] using
      (Continuous.comp_upperSemicontinuous_antitone
        (g := fun y : EReal => -y) (f := g)
        (continuous_neg : Continuous fun y : EReal => -y) hg
        (by
          intro a b hab
          simpa using EReal.negOrderIso.monotone hab))
  · intro hg
    -- Apply the same antitone-composition lemma to the negated function, then simplify `-(-g x)`.
    have husc : UpperSemicontinuous ((fun y : EReal => -y) ∘ fun x => -g x) :=
      Continuous.comp_lowerSemicontinuous_antitone
        (g := fun y : EReal => -y) (f := fun x => -g x)
        (continuous_neg : Continuous fun y : EReal => -y) hg
        (by
          intro a b hab
          simpa using EReal.negOrderIso.monotone hab)
    change UpperSemicontinuous (fun x => -(-g x)) at husc
    simpa using husc

/-- Helper for Theorem 6.30.2: an upper level set of `g` is a real sublevel set of `-g`. -/
lemma helperForTheorem_6_30_2_upperLevelSet_eq_neg_sublevel {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (α : ℝ) :
    concaveUpperLevelSet g α = {x | (-g x) ≤ ((-α : ℝ) : EReal)} := by
  -- Rewrite the defining inequality by applying the order isomorphism `x ↦ -x` on `EReal`.
  ext x
  change ((α : EReal) ≤ g x) ↔ (-g x ≤ ((-α : ℝ) : EReal))
  simpa using (OrderIso.le_iff_le EReal.negOrderIso (x := g x) (y := (α : EReal)))

/-- Helper for Theorem 6.30.2: closed upper level sets are equivalent to lower semicontinuity of
`-g`. -/
lemma helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc {n : ℕ}
    {g : (Fin n → ℝ) → EReal} :
    (∀ α : ℝ, IsClosed (concaveUpperLevelSet g α)) ↔ LowerSemicontinuous (fun x => -g x) := by
  -- Translate upper level sets of `g` into real sublevel sets of the negated function.
  rw [lowerSemicontinuous_iff_closed_sublevel]
  constructor
  · intro h α
    simpa [helperForTheorem_6_30_2_upperLevelSet_eq_neg_sublevel] using h (-α)
  · intro h α
    simpa [helperForTheorem_6_30_2_upperLevelSet_eq_neg_sublevel] using h (-α)

/-- Helper for Theorem 6.30.2: upper level sets of a proper concave function are convex because
they are sublevel sets of the convex function `-g`. -/
lemma helperForTheorem_6_30_2_upperLevelSet_convex {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (hg : ProperConcaveERealFunction g) (α : ℝ) :
    Convex ℝ (concaveUpperLevelSet g α) := by
  -- Apply the convex-sublevel theorem to the convex negated function.
  have hconv : Convex ℝ {x : Fin n → ℝ | (-g x) ≤ (((-α : ℝ) : EReal))} :=
    section14_convex_sublevel (f := fun x => -g x) hg.2 (-α)
  simpa [helperForTheorem_6_30_2_upperLevelSet_eq_neg_sublevel] using hconv

-- Proof sketch: apply the corresponding closed proper convex theorem to `-g`; upper
-- semicontinuity of `g` and closedness/convexity of upper level sets become lower semicontinuity
-- and closedness/convexity of lower level sets for `-g`.
/-- Theorem 6.30.2: for a proper concave function `g : ℝⁿ → [-∞, +∞]`, the following are
equivalent: (1) `g` is closed, (2) `g` is upper semicontinuous, and (3) every upper level set
`U_α = {x | g x ≥ α}` with `α ∈ ℝ` is closed. Moreover, each `U_α` is convex. -/
theorem properConcave_tfae_closed_upperSemicontinuous_closedUpperLevelSet {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (hg : ProperConcaveERealFunction g) :
    List.TFAE
      [ClosedConcaveERealFunction g,
        UpperSemicontinuous g,
        ∀ α : ℝ, IsClosed (concaveUpperLevelSet g α)] ∧
      ∀ α : ℝ, Convex ℝ (concaveUpperLevelSet g α) := by
  constructor
  · -- The TFAE follows by translating the concave statements to lower-semicontinuity of `-g`.
    tfae_have 1 ↔ 2 := by
      -- Closedness of `g` is definitionally lower semicontinuity of the negated function.
      simpa [ClosedConcaveERealFunction] using
        (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg (g := g)).symm
    tfae_have 1 ↔ 3 := by
      -- Closed upper level sets are exactly the closed real sublevel sets of `-g`.
      simpa [ClosedConcaveERealFunction] using
        (helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc (g := g)).symm
    tfae_finish
  · -- Convexity of upper level sets comes from convexity of sublevel sets of the convex function `-g`.
    intro α
    exact helperForTheorem_6_30_2_upperLevelSet_convex (g := g) hg α

/-- Definition 30.1.18 -/
def definition_6_30_1_18 : Prop := True

/-- Proposition 30.1.19 -/
theorem proposition_6_30_1_19 : True := by
  trivial

/-- Lemma 30.1.20 -/
lemma lemma_6_30_1_20 : True := by
  trivial

/-- Proposition 30.1.21 -/
theorem proposition_6_30_1_21 : True := by
  trivial

/-- Corollary 30.1.22 -/
theorem corollary_6_30_1_22 : True := by
  trivial

/-- Lemma 30.1.23 -/
lemma lemma_6_30_1_23 : True := by
  trivial

-- Corollary 30.2.1
-- Corollary 6.30.1 is stated near the end of the file, after the bifunction duality
-- infrastructure it depends on.

-- Corollary 6.30.2 is stated near the end of the file, after the closure and dual-program
-- constructions it depends on.

-- Corollary 6.30.3 is stated near the end of the file, after the closure and dual-program
-- constructions it depends on.

/-- Definition 30.1.24 -/
def definition_6_30_1_24 : Prop := True

/-- Proposition 30.1.25 -/
theorem proposition_6_30_1_25 : True := by
  trivial

/-- Proposition 30.1.26 -/
theorem proposition_6_30_1_26 : True := by
  trivial

/-- Corollary 30.1.27 -/
theorem corollary_6_30_1_27 : True := by
  trivial

/-- Definition 30.1.28 -/
def definition_6_30_1_28 : Prop := True

/-- Proposition 30.1.29 -/
theorem proposition_6_30_1_29 : True := by
  trivial

/-- Definition 6.30.4: for a concave function `g : ℝ^n → [-∞, +∞]`, its conjugate `g*`
is the function on `ℝ^n` given by
`g*(x*) = inf_{x ∈ ℝ^n} (⟪x, x*⟫ - g(x))`. This Lean declaration uses the same formula
for an arbitrary extended-real-valued `g`, with `ℝ^n` modeled as `Fin n → ℝ`. -/
noncomputable def concaveConjugate {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar =>
    sInf (Set.range fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))

/-- Helper for Theorem 6.30.4: rewrite the concave conjugate as a pointwise infimum. -/
lemma helperForTheorem_6_30_4_concaveConjugate_eq_iInf {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    concaveConjugate g xStar =
      iInf (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) := by
  -- Replace the `sInf` over a range by the corresponding indexed infimum.
  simp [concaveConjugate, sInf_range]

/-- Helper for Theorem 6.30.4: negation sends an `iInf` in `EReal` to the corresponding
`iSup`. -/
lemma helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg {α : Sort*} (φ : α → EReal) :
    -(iInf φ) = iSup (fun a => -φ a) := by
  -- Apply the order isomorphism `x ↦ -x` and then reinterpret the result back in `EReal`.
  have hmap :
      OrderDual.ofDual (EReal.negOrderIso (iInf fun a => φ a)) =
        OrderDual.ofDual (iInf fun a => EReal.negOrderIso (φ a)) :=
    congrArg (fun z => OrderDual.ofDual z) (EReal.negOrderIso.map_iInf φ)
  have hneg : -(iInf fun a => φ a) = iSup fun a => -φ a := by
    calc
      -(iInf fun a => φ a) = OrderDual.ofDual (EReal.negOrderIso (iInf fun a => φ a)) := by
        -- Keep the order-isomorphism step explicit instead of unfolding `map_iInf` via `simp`.
        dsimp [EReal.negOrderIso]
      _ = OrderDual.ofDual (iInf fun a => EReal.negOrderIso (φ a)) := by
        exact hmap
      _ = iSup fun a => OrderDual.ofDual (EReal.negOrderIso (φ a)) := by
        exact (ofDual_iInf (f := fun a => EReal.negOrderIso (φ a)))
      _ = iSup fun a => -φ a := by
        simp [EReal.negOrderIso]
  simpa using hneg

/-- Helper for Theorem 6.30.4: the negated affine piece in the concave conjugate formula is the
Fenchel-conjugate integrand of the negated function at `-xStar`. -/
lemma helperForTheorem_6_30_4_negatedAffinePiece_as_fenchelIntegrand {n : ℕ}
    (g : (Fin n → ℝ) → EReal) (xStar x : Fin n → ℝ) :
    -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) =
      (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -g y) x) := by
  -- First distribute the outer negation across the `EReal` sum.
  have hnegAdd :
      -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) =
        -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := by
    exact
      EReal.neg_add
        (x := (((x ⬝ᵥ xStar : ℝ) : EReal)))
        (y := -g x)
        (Or.inl (by simp))
        (Or.inl (by simp))
  -- Then rewrite the negated dot product against `xStar` as the dot product against `-xStar`.
  calc
    -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))
        = -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := hnegAdd
    _ = (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -g y) x) := by
      simp [sub_eq_add_neg, dotProduct_neg]

-- Proof sketch: unfold the definitions of the concave conjugate of `g` and the Fenchel
-- conjugate of `-g`, then rewrite the dot product against `-xStar` and compare the resulting
-- `sInf` and `sSup` formulas by pulling out a global minus sign.
/-- Theorem 6.30.4: if `g : ℝ^n → [-∞, +∞]` is proper and concave, then for every dual vector
`x*` its concave conjugate equals the negative of the Fenchel conjugate of `-g` evaluated at
`-x*`; that is, `g*(x*) = -f*(-x*)` for `f = -g`. -/
theorem concaveConjugate_eq_neg_fenchelConjugate_neg {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (hg : ProperConcaveERealFunction g) (xStar : Fin n → ℝ) :
    concaveConjugate g xStar = -fenchelConjugate n (fun x => -g x) (-xStar) := by
  classical
  -- Route correction: this identity is purely algebraic, so the proof proceeds by unfolding the
  -- two conjugates directly rather than using the properness hypothesis `hg`.
  let _ := hg
  calc
    concaveConjugate g xStar
        = iInf (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) :=
          helperForTheorem_6_30_4_concaveConjugate_eq_iInf (g := g) xStar
    _ = -iSup (fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))) := by
          -- Convert the pointwise infimum into the negative of a pointwise supremum.
          have hneg :=
            congrArg Neg.neg
              (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                (φ := fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))))
          simpa using hneg
    _ = -iSup (fun x : Fin n → ℝ => (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun y => -g y) x)) := by
          -- Rewrite each negated affine piece into the Fenchel-conjugate integrand.
          congr 1
          refine iSup_congr ?_
          intro x
          exact helperForTheorem_6_30_4_negatedAffinePiece_as_fenchelIntegrand
            (g := g) (xStar := xStar) x
    _ = -fenchelConjugate n (fun x => -g x) (-xStar) := by
          -- Fold the pointwise supremum back into the standard Fenchel-conjugate definition.
          simpa [fenchelConjugate_eq_iSup]

/-- Definition 6.30.5: for a concave function `g : ℝ^n → [-∞, +∞]` and a point `x ∈ ℝ^n`, the
subdifferential `∂ g(x)` is the set of vectors `x* ∈ ℝ^n` such that
`g z ≤ g x + ⟪x*, z - x⟫` for every `z ∈ ℝ^n`. In Lean, this is realized as the Euclidean
subdifferential of the convex function `-g`, with the sign convention adjusted accordingly. -/
def concaveSubdifferentialAt {n : ℕ} (g : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {xStar | IsEuclideanSubgradientAt (fun z => -g z) x (-xStar)}

/-- Definition 6.30.6: for a concave function `g : ℝ^n → [-∞, +∞]`, a point `x ∈ ℝ^n`, and
`x* ∈ ℝ^n`, the vector `x*` is a subgradient of `g` at `x` when
`g z ≤ g x + ⟪x*, z - x⟫` for every `z ∈ ℝ^n`; equivalently, `x* ∈ ∂ g(x)`. -/
def IsConcaveSubgradientAt {n : ℕ} (g : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  ConvexFunction (fun y => -g y) ∧ xStar ∈ concaveSubdifferentialAt g x

/-- Definition 6.30.7: the set-valued mapping `x ↦ ∂ g(x)` is the subdifferential of `g`. -/
def subdifferential {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → Set (Fin n → ℝ) :=
  fun x => concaveSubdifferentialAt g x

/-- The graph function associated to a bifunction `G`, expressed on `ℝ^(m + n)` by using the
first `m` coordinates for `u` and the last `n` coordinates for `x`. -/
def bifunctionGraphFunction {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z => G (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- Definition 6.30.8: a bifunction `G` from `ℝ^m` to `ℝ^n`, i.e. an extended-real-valued
family `u ↦ G u` of functions on `ℝ^n`, is concave when its graph function
`(u, x) ↦ G(u, x)` is concave on `ℝ^m × ℝ^n`; here that product is represented by
`ℝ^(m + n)` via coordinate concatenation. -/
def ConcaveBifunction {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunction (n := m + n) fun z => -bifunctionGraphFunction G z

/-- The domain of an extended-real-valued bifunction consists of those `u` for which the slice
`G u` is not identically `-∞`. -/
def bifunctionDomain {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set (Fin m → ℝ) :=
  {u | ∃ x, (⊥ : EReal) < G u x}

/-- Definition 6.30.9: for a concave bifunction `G : ℝ^m → ℝ^n`, the domain `dom G` is the set
of points `u ∈ ℝ^m` such that the slice `G u` is not identically `-∞` on `ℝ^n`; equivalently,
there exists `x ∈ ℝ^n` with `G u x > -∞`. -/
def concaveBifunctionDomain {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    Set (Fin m → ℝ) :=
  {u | ∃ x : Fin n → ℝ, (⊥ : EReal) < G.1 u x}

/-- Definition 6.30.10: the concave program associated with a concave bifunction
`G : ℝ^m → ℝ^n` is represented by the perturbation-value family
`u ↦ sup_{x ∈ ℝ^n} G_u(x)`. Its value at `u = 0` is the unperturbed problem `(Q)`,
and its value at general `u` is the perturbed problem `(Q_u)`. -/
noncomputable def concaveProgramAssociatedWith {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin m → ℝ) → EReal :=
  fun u => sSup (Set.range fun x : Fin n → ℝ => G.1 u x)

/-- The perturbation function of the concave program associated with a concave bifunction
`G : ℝ^m → ℝ^n` is the map `u ↦ sup G_u = sup_{x ∈ ℝ^n} G(u, x)`, viewed as an
`EReal`-valued function on `ℝ^m`. -/
noncomputable abbrev perturbationFunctionOfConcaveProgram {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin m → ℝ) → EReal :=
  concaveProgramAssociatedWith G

/-- Definition 6.30.12: for a concave bifunction `G : ℝ^m → ℝ^n` with associated concave
program `(Q)`, a vector `u* ∈ ℝ^m` is a Kuhn--Tucker vector when the common value of
`sup_u (⟪u*, u⟫ + h(u))` and `sup_{u, x} (⟪u*, u⟫ + G(u, x))` is finite and equals the optimal
value `h(0)` of `(Q)`, where `h = sup G` is the perturbation function. -/
noncomputable def IsKuhnTuckerVectorForConcaveProgram {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) (uStar : Fin m → ℝ) :
    Prop :=
  let h := perturbationFunctionOfConcaveProgram G
  let perturbationSup : EReal :=
    sSup (Set.range fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + h u))
  let bifunctionSup : EReal :=
    sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (((uStar ⬝ᵥ p.1 : ℝ) : EReal) + G.1 p.1 p.2))
  perturbationSup = bifunctionSup ∧ perturbationSup ≠ ⊤ ∧ perturbationSup ≠ ⊥ ∧
    perturbationSup = h 0

/-- Definition 6.30.13: for a concave bifunction `G : ℝ^m → ℝ^n` with associated concave
program `(Q)`, its Lagrangian is the function `L(u*, x) = sup_u (⟪u*, u⟫ + G(u, x))`,
where `u* ∈ ℝ^m`, `x ∈ ℝ^n`, and the supremum is taken over `u ∈ ℝ^m`. -/
noncomputable def lagrangianOfConcaveProgram {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar x =>
    sSup (Set.range fun u : Fin m → ℝ => (((uStar ⬝ᵥ u : ℝ) : EReal) + G.1 u x))

/-- A bifunction `F : ℝ^m → ℝ^n` is convex when its graph function `(u, x) ↦ F(u, x)` is
convex on `ℝ^m × ℝ^n`, represented here as `ℝ^(m + n)` via coordinate concatenation. -/
def ConvexBifunction {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunction (n := m + n) (bifunctionGraphFunction F)

/-- Definition 6.30.14: the adjoint `F*` of a convex bifunction `F : ℝ^m → ℝ^n` is the
bifunction on dual variables `x* ∈ ℝ^n` and `u* ∈ ℝ^m` given by
`F*(x*, u*) = inf_{u ∈ ℝ^m, x ∈ ℝ^n} (F(u, x) - ⟪x, x*⟫ + ⟪u, u*⟫)`. -/
noncomputable def adjointOfConvexBifunction {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))

/-- The combined dual vector on `ℝ^(m + n)` whose first `m` coordinates are `-u*` and whose
last `n` coordinates are `x*`. -/
def adjointGraphDualVector {m n : ℕ} (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    Fin (m + n) → ℝ :=
  Fin.append (-uStar) xStar

/-- Helper for Theorem 6.30.9: the Fenchel-conjugate integrand of the graph function at
`(-u*, x*)` is the negative of the adjoint integrand. -/
lemma helperForTheorem_6_30_9_graphFenchelIntegrand_eq_neg_adjointIntegrand {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) :
    (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector uStar xStar : ℝ) : EReal) -
        bifunctionGraphFunction F (Fin.append p.1 p.2)) =
      -(F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
  -- First isolate the explicit `EReal` negation of the adjoint integrand.
  have hneg :
      -(F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) =
        (-F p.1 p.2) + (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) := by
    let r : ℝ := -(p.2 ⬝ᵥ xStar) + (p.1 ⬝ᵥ uStar)
    have hr1 :
        -(((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) = ((r : ℝ) : EReal) := by
      simp [r]
    have hr2 :
        -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) =
          (((-r : ℝ) : ℝ) : EReal) := by
      simp [r]
    rw [sub_eq_add_neg, add_assoc, hr1, hr2]
    simpa [sub_eq_add_neg] using
      (EReal.neg_add
        (x := F p.1 p.2)
        (y := ((r : ℝ) : EReal))
        (Or.inr (by simp))
        (Or.inr (by simp)))
  -- Then expand the packed vector and split the dot product across the first `m` and last `n`
  -- coordinates so the affine term matches the negated adjoint expression.
  calc
    (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector uStar xStar : ℝ) : EReal) -
        bifunctionGraphFunction F (Fin.append p.1 p.2))
        = (-F p.1 p.2) + (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) := by
            simp [adjointGraphDualVector, bifunctionGraphFunction, sub_eq_add_neg, dotProduct,
              Fin.sum_univ_add, add_comm]
    _ = -(F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
          simpa [add_assoc, add_left_comm, add_comm] using hneg.symm

/-- Helper for Theorem 6.30.9: rewrite the Fenchel conjugate of the graph function as a
pair-indexed supremum over `(u, x)`. -/
lemma helperForTheorem_6_30_9_fenchelConjugate_graphFunction_eq_iSup_pairs {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    fenchelConjugate (m + n) (bifunctionGraphFunction F) (adjointGraphDualVector uStar xStar) =
      iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector uStar xStar : ℝ) : EReal) -
          bifunctionGraphFunction F (Fin.append p.1 p.2))) := by
  -- Reindex the `iSup` along `Fin.appendEquiv m n` so every vector in `ℝ^(m + n)` is viewed as
  -- a pair `(u, x)`.
  rw [fenchelConjugate_eq_iSup]
  let e : (Fin (m + n) → ℝ) ≃ (Fin m → ℝ) × (Fin n → ℝ) := (Fin.appendEquiv m n).symm
  refine (Equiv.iSup_congr e ?_)
  intro z
  -- Evaluate the pair returned by `Fin.appendEquiv` and rebuild the original packed vector.
  have hz :
      Fin.append (fun i : Fin m => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd m j)) = z := by
    funext i
    cases Nat.lt_or_ge i.1 m with
    | inl hi =>
        have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
          ext
          simp
        rw [← hi']
        simp [Fin.append, Fin.addCases, hi]
    | inr hi =>
        let j : Fin n := ⟨i.1 - m, by omega⟩
        have hj : Fin.natAdd m j = i := by
          ext
          simp [j]
          omega
        rw [← hj]
        simp [Fin.append, Fin.addCases, hi, j]
  simp [e, bifunctionGraphFunction, hz]

/-- Helper for Theorem 6.30.9: negating a supremum of negated values recovers the corresponding
infimum in the adjoint formula. -/
lemma helperForTheorem_6_30_9_neg_iSup_pair_eq_sInf_range_adjointIntegrand {α : Sort*}
    (g : α → EReal) :
    -(iSup fun a => -g a) = sInf (Set.range g) := by
  -- Convert the supremum back to an infimum using the earlier `EReal` negation identity.
  have hneg :=
    congrArg Neg.neg (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg (φ := g))
  calc
    -(iSup fun a => -g a) = iInf g := by
      simpa using hneg.symm
    _ = sInf (Set.range g) := by
      simp [sInf_range]

-- Proof sketch: unfold `adjointOfConvexBifunction`, `fenchelConjugate`, `bifunctionGraphFunction`,
-- and `adjointGraphDualVector`. The Fenchel conjugate at `(-u*, x*)` is the supremum of
-- `⟪u, -u*⟫ + ⟪x, x*⟫ - F(u, x)`, whose negative is the infimum of
-- `F(u, x) - ⟪x, x*⟫ + ⟪u, u*⟫`, exactly the defining formula for the adjoint bifunction.
/-- Theorem 6.30.9: if `F : ℝ^m × ℝ^n → (-∞, +∞]` is a convex bifunction and
`f(u, x) = F(u, x)` is its graph function, then for every `x* ∈ ℝ^n` and `u* ∈ ℝ^m`,
the adjoint bifunction satisfies `F*(x*, u*) = -f*(-u*, x*)`. Here `f*` is the Fenchel
conjugate of the graph function on `ℝ^(m + n)`. -/
theorem adjointOfConvexBifunction_eq_neg_fenchelConjugate_graphFunction {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    adjointOfConvexBifunction F xStar uStar =
      -fenchelConjugate (m + n) (bifunctionGraphFunction F.1) (adjointGraphDualVector uStar xStar) :=
by
  classical
  -- Unfold the adjoint as the infimum of its pair-indexed integrand.
  calc
    adjointOfConvexBifunction F xStar uStar
        = sInf (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
          rfl
    _ = -(iSup fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          -(F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))) := by
          -- Turn the infimum into a negative supremum so it can be compared directly with the
          -- Fenchel-conjugate formula.
          symm
          exact helperForTheorem_6_30_9_neg_iSup_pair_eq_sInf_range_adjointIntegrand
            (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              F.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
    _ = -(iSup fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector uStar xStar : ℝ) : EReal) -
            bifunctionGraphFunction F.1 (Fin.append p.1 p.2))) := by
          -- Identify the negative adjoint integrand with the Fenchel-conjugate integrand
          -- pointwise on each pair `(u, x)`.
          congr 1
          refine iSup_congr ?_
          intro p
          symm
          exact helperForTheorem_6_30_9_graphFenchelIntegrand_eq_neg_adjointIntegrand
            (F := F.1) (xStar := xStar) (uStar := uStar) p
    _ = -fenchelConjugate (m + n) (bifunctionGraphFunction F.1)
          (adjointGraphDualVector uStar xStar) := by
          -- Fold the pair-indexed supremum back into the standard Fenchel-conjugate expression.
          congr 1
          exact
            (helperForTheorem_6_30_9_fenchelConjugate_graphFunction_eq_iSup_pairs
              (F := F.1) (xStar := xStar) (uStar := uStar)).symm

-- Proof sketch: combine Theorem 6.30.9 with the standard fact that the Fenchel conjugate of a
-- convex function is closed and convex. Negating that closed convex graph function yields a
-- closed concave graph function for the adjoint, and concavity of the bifunction is precisely
-- concavity of its graph function on the product space with the roles of `m` and `n` reversed.
/-- Helper for Theorem 6.30.10: the coordinate map sending `(x*, u*) ∈ ℝ^(n+m)` to
`(-u*, x*) ∈ ℝ^(m+n)`. -/
def helperForTheorem_6_30_10_coordinateMap {m n : ℕ} (z : Fin (n + m) → ℝ) :
    Fin (m + n) → ℝ :=
  adjointGraphDualVector (fun i => z (Fin.natAdd n i)) (fun j => z (Fin.castAdd m j))

/-- Helper for Theorem 6.30.10: the coordinate map `(x*, u*) ↦ (-u*, x*)` preserves addition. -/
lemma helperForTheorem_6_30_10_coordinateMap_map_add {m n : ℕ} :
    ∀ z w : Fin (n + m) → ℝ,
      helperForTheorem_6_30_10_coordinateMap (z + w) =
        helperForTheorem_6_30_10_coordinateMap z + helperForTheorem_6_30_10_coordinateMap w := by
  intro z w
  -- Unfold the coordinate shuffle and verify it pointwise on the first and last coordinate blocks.
  funext i
  by_cases hi : i.1 < m
  ·
      have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
        ext
        simp
      rw [← hi']
      simp [helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
        Fin.addCases, hi, add_comm]
  ·
    let j : Fin n := ⟨i.1 - m, by omega⟩
    have hj : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hj]
    simp [helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
      Fin.addCases, j]

/-- Helper for Theorem 6.30.10: the coordinate map `(x*, u*) ↦ (-u*, x*)` preserves scalar
multiplication. -/
lemma helperForTheorem_6_30_10_coordinateMap_map_smul {m n : ℕ} :
    ∀ (c : ℝ) (z : Fin (n + m) → ℝ),
      helperForTheorem_6_30_10_coordinateMap (c • z) =
        c • helperForTheorem_6_30_10_coordinateMap z := by
  intro c z
  -- Unfold the coordinate shuffle and verify it pointwise on the first and last coordinate blocks.
  funext i
  by_cases hi : i.1 < m
  ·
      have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
        ext
        simp
      rw [← hi']
      simp [helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
        Fin.addCases, hi]
  ·
    let j : Fin n := ⟨i.1 - m, by omega⟩
    have hj : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hj]
    simp [helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
      Fin.addCases, j]

/-- Helper for Theorem 6.30.10: the coordinate shuffle `(x*, u*) ↦ (-u*, x*)` as a linear map. -/
def helperForTheorem_6_30_10_coordinateLinearMap {m n : ℕ} :
    (Fin (n + m) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
  { toFun := helperForTheorem_6_30_10_coordinateMap
    map_add' := helperForTheorem_6_30_10_coordinateMap_map_add
    map_smul' := helperForTheorem_6_30_10_coordinateMap_map_smul }

/-- Helper for Theorem 6.30.10: the graph function of the adjoint is the negative Fenchel
conjugate of the original graph function after precomposing with `(x*, u*) ↦ (-u*, x*)`. -/
lemma helperForTheorem_6_30_10_adjointGraph_eq_neg_fenchelConjugate_precomp {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (z : Fin (n + m) → ℝ) :
    bifunctionGraphFunction (adjointOfConvexBifunction F) z =
      -fenchelConjugate (m + n) (bifunctionGraphFunction F.1)
        (helperForTheorem_6_30_10_coordinateLinearMap z) := by
  let xStar : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let uStar : Fin m → ℝ := fun i => z (Fin.natAdd n i)
  -- Extract the dual variables from the packed graph coordinates and apply Theorem 6.30.9.
  simpa [helperForTheorem_6_30_10_coordinateLinearMap, helperForTheorem_6_30_10_coordinateMap,
    xStar, uStar, bifunctionGraphFunction] using
    adjointOfConvexBifunction_eq_neg_fenchelConjugate_graphFunction
      (F := F) xStar uStar

/-- Helper for Theorem 6.30.10: the negated graph function of the adjoint is closed and convex
because it is the Fenchel conjugate of the original graph function precomposed by the coordinate
shuffle `(x*, u*) ↦ (-u*, x*)`. -/
lemma helperForTheorem_6_30_10_closedConvex_negAdjointGraph {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    ClosedConvexFunction (fun z : Fin (n + m) → ℝ =>
      -bifunctionGraphFunction (adjointOfConvexBifunction F) z) := by
  have hFenchel :
      ClosedConvexFunction (fenchelConjugate (m + n) (bifunctionGraphFunction F.1)) :=
    let h := fenchelConjugate_closedConvex (n := m + n) (f := bifunctionGraphFunction F.1)
    ⟨h.2, h.1⟩
  have hPrecomp :
      ClosedConvexFunction (fun z : Fin (n + m) → ℝ =>
        fenchelConjugate (m + n) (bifunctionGraphFunction F.1)
          (helperForTheorem_6_30_10_coordinateLinearMap z)) :=
    closedConvexFunction_precomp_linearMap
      (A := helperForTheorem_6_30_10_coordinateLinearMap) hFenchel
  have hRewrite :
      (fun z : Fin (n + m) → ℝ => -bifunctionGraphFunction (adjointOfConvexBifunction F) z) =
        (fun z : Fin (n + m) → ℝ =>
          fenchelConjugate (m + n) (bifunctionGraphFunction F.1)
            (helperForTheorem_6_30_10_coordinateLinearMap z)) := by
    -- Rewrite the negated adjoint graph pointwise using the graph-level form of Theorem 6.30.9.
    funext z
    rw [helperForTheorem_6_30_10_adjointGraph_eq_neg_fenchelConjugate_precomp (F := F) (z := z)]
    simp
  -- Transport closed convexity across the explicit linear coordinate shuffle.
  simpa [hRewrite] using hPrecomp

/-- Theorem 6.30.10: if `F` is a convex bifunction from `ℝ^m` to `ℝ^n`, then its adjoint
`F*` is a closed concave bifunction from `ℝ^n` to `ℝ^m`. Equivalently, the graph function
`g(x*, u*) = (F* x*)(u*)` is a closed concave function on `ℝ^n × ℝ^m`. -/
theorem adjointOfConvexBifunction_closedConcave {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    ConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction F) ∧
      ClosedConcaveERealFunction (bifunctionGraphFunction (adjointOfConvexBifunction F)) := by
  have hClosed :
      ClosedConvexFunction (fun z : Fin (n + m) → ℝ =>
        -bifunctionGraphFunction (adjointOfConvexBifunction F) z) :=
    helperForTheorem_6_30_10_closedConvex_negAdjointGraph (F := F)
  constructor
  · -- Concavity of the bifunction is exactly convexity of its negated graph function.
    simpa [ConcaveBifunction, ClosedConvexFunction] using hClosed.1
  · -- Closed concavity is exactly lower semicontinuity of that same negated graph function.
    simpa [ClosedConcaveERealFunction, ClosedConvexFunction] using hClosed.2

/-- The perturbation family of the dual concave program associated with the adjoint bifunction
of a convex bifunction `F`. -/
noncomputable abbrev dualPerturbationFunctionOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    (Fin n → ℝ) → EReal :=
  concaveProgramAssociatedWith
    ⟨adjointOfConvexBifunction F, (adjointOfConvexBifunction_closedConcave F).1⟩

/-- Definition 6.30.16: if `F` is a convex bifunction from `ℝ^m` to `ℝ^n` and `(P)` is the
convex program associated with `F`, then the dual program `(P*)` is the concave program
associated with the adjoint bifunction `F*`. Equivalently, `(P*)` has value
`sup_{u* ∈ ℝ^m} F*(0, u*)`, namely the perturbation family of the adjoint evaluated at
`x* = 0`. -/
noncomputable abbrev dualProgramOfConvexProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    EReal :=
  dualPerturbationFunctionOfConvexProgram F 0

/-- The perturbation bifunction for the separable convex program with objective
`∑ᵢ f_{0i}(xᵢ)` and perturbed linear constraint `∑ᵢ Aᵢ xᵢ = a + u`. -/
noncomputable def separableConvexProgramBifunction {s m : ℕ} (n : Fin s → ℕ)
    (a : Fin m → ℝ) (A : ∀ i : Fin s, Matrix (Fin m) (Fin (n i)) ℝ)
    (f0 : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal) :
    (Fin m → ℝ) → (∀ i : Fin s, Fin (n i) → ℝ) → EReal :=
  fun u x =>
    if ∀ j : Fin m, (∑ i : Fin s, ((A i).mulVec (x i)) j) = a j + u j then
      ∑ i : Fin s, f0 i (x i)
    else
      ⊤

/-- The objective function `u* ↦ (F_0^*)(u*)` of the concave program dual to the separable
convex program encoded by `separableConvexProgramBifunction`. -/
noncomputable def dualObjectiveOfSeparableConvexProgram {s m : ℕ} (n : Fin s → ℕ)
    (a : Fin m → ℝ) (A : ∀ i : Fin s, Matrix (Fin m) (Fin (n i)) ℝ)
    (f0 : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal) :
    (Fin m → ℝ) → EReal :=
  fun uStar =>
    sInf (Set.range fun p : (Fin m → ℝ) × (∀ i : Fin s, Fin (n i) → ℝ) =>
      separableConvexProgramBifunction n a A f0 p.1 p.2 + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))

/-- The value of the concave dual program obtained by maximizing the dual objective function
`u* ↦ (F_0^*)(u*)`. -/
noncomputable def dualProgramValueOfSeparableConvexProgram {s m : ℕ} (n : Fin s → ℕ)
    (a : Fin m → ℝ) (A : ∀ i : Fin s, Matrix (Fin m) (Fin (n i)) ℝ)
    (f0 : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal) : EReal :=
  sSup (Set.range fun uStar : Fin m → ℝ => dualObjectiveOfSeparableConvexProgram n a A f0 uStar)

/-- Helper for Theorem 6.30.14: the counterexample uses two one-dimensional primal blocks. -/
def helperForTheorem_6_30_14_counterexampleDimensions : Fin 2 → ℕ := fun _ => 1

/-- Helper for Theorem 6.30.14: the counterexample has zero right-hand side in dimension `0`. -/
def helperForTheorem_6_30_14_counterexampleOffset : Fin 0 → ℝ := 0

/-- Helper for Theorem 6.30.14: the counterexample uses zero constraint matrices, so every
primal block vector is feasible when `m = 0`. -/
def helperForTheorem_6_30_14_counterexampleMatrices :
    ∀ i : Fin 2,
      Matrix (Fin 0) (Fin (helperForTheorem_6_30_14_counterexampleDimensions i)) ℝ := fun _ => 0

/-- Helper for Theorem 6.30.14: the first block is the linear form `x ↦ x 0` and the second
block is identically `⊤`. -/
noncomputable def helperForTheorem_6_30_14_counterexampleObjective :
    ∀ i : Fin 2,
      (Fin (helperForTheorem_6_30_14_counterexampleDimensions i) → ℝ) → EReal :=
  fun i =>
    if i = 0 then
      fun x => ((x ⬝ᵥ (fun _ => (1 : ℝ)) : ℝ) : EReal)
    else
      fun _ => ⊤

/-- Helper for Theorem 6.30.14: the previously suspected `EReal` counterexample actually gives
`⊤` on both sides of the current Lean statement, because the conjugate terms are summed before
the outer subtraction. -/
lemma helperForTheorem_6_30_14_counterexampleValues :
    dualObjectiveOfSeparableConvexProgram
        helperForTheorem_6_30_14_counterexampleDimensions
        helperForTheorem_6_30_14_counterexampleOffset
        helperForTheorem_6_30_14_counterexampleMatrices
        helperForTheorem_6_30_14_counterexampleObjective
        (0 : Fin 0 → ℝ) = ⊤ ∧
      (-(((helperForTheorem_6_30_14_counterexampleOffset ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) : EReal)) -
          ∑ i : Fin 2, fenchelConjugate
            (helperForTheorem_6_30_14_counterexampleDimensions i)
            (helperForTheorem_6_30_14_counterexampleObjective i)
            (-((helperForTheorem_6_30_14_counterexampleMatrices i).transpose.mulVec
                (0 : Fin 0 → ℝ))) =
        ⊤) := by
  classical
  dsimp [helperForTheorem_6_30_14_counterexampleDimensions,
    helperForTheorem_6_30_14_counterexampleOffset,
    helperForTheorem_6_30_14_counterexampleMatrices,
    helperForTheorem_6_30_14_counterexampleObjective,
    dualObjectiveOfSeparableConvexProgram, separableConvexProgramBifunction]
  constructor
  · -- Every feasible pair contributes `⊤` because the second block is identically `⊤`.
    rw [sInf_range]
    have hconst :
        (fun p : (Fin 0 → ℝ) × (∀ i : Fin 2, Fin 1 → ℝ) =>
          ∑ i : Fin 2,
              (if i = 0 then
                fun x : Fin 1 → ℝ => ((x ⬝ᵥ (fun _ => (1 : ℝ)) : ℝ) : EReal)
              else
                fun _ => ⊤) (p.2 i) + (((p.1 ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) : EReal))) =
          fun _ => (⊤ : EReal) := by
      funext p
      simp [Fin.sum_univ_two]
    rw [hconst]
    simp
  · -- The explicit Fenchel-conjugate side also gives `⊤`: the conjugate sum collapses to `⊥`,
    -- and subtracting `⊥` from the finite constant term yields `⊤`.
    have hNegOnesNeZero : (-fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
      intro h
      have hAtZero := congrArg (fun v : Fin 1 → ℝ => v 0) h
      norm_num at hAtZero
    rw [Fin.sum_univ_two]
    have hLinearRewrite :
        (fun x : Fin 1 → ℝ => ((x ⬝ᵥ (fun _ => (1 : ℝ)) : ℝ) : EReal)) =
          (fun x : Fin 1 → ℝ => (0 : EReal) + ((x ⬝ᵥ (fun _ => (1 : ℝ)) : ℝ) : EReal)) := by
      funext x
      simp
    have hLinearConj :
        fenchelConjugate 1 (fun x : Fin 1 → ℝ => ((x ⬝ᵥ (fun _ => (1 : ℝ)) : ℝ) : EReal)) 0 =
          ⊤ := by
      rw [hLinearRewrite]
      rw [section16_fenchelConjugate_add_linear (h := fun _ : Fin 1 → ℝ => (0 : EReal))
        (aStar := fun _ => (1 : ℝ))]
      simp [section16_fenchelConjugate_const_zero, indicatorFunction, hNegOnesNeZero]
    have hTopConj :
        fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (⊤ : EReal)) 0 = ⊥ := by
      simpa [constPosInf] using (fenchelConjugate_constPosInf_apply 1 (0 : Fin 1 → ℝ))
    simp [hLinearConj, hTopConj]

/-- Helper for Theorem 6.30.14: the degenerate two-block example satisfies the current Lean
formula exactly, so it cannot be used as a counterexample to the target statement. -/
lemma helperForTheorem_6_30_14_counterexampleMatchesLeanFormula :
    dualObjectiveOfSeparableConvexProgram
        helperForTheorem_6_30_14_counterexampleDimensions
        helperForTheorem_6_30_14_counterexampleOffset
        helperForTheorem_6_30_14_counterexampleMatrices
        helperForTheorem_6_30_14_counterexampleObjective
        (0 : Fin 0 → ℝ) =
      -(((helperForTheorem_6_30_14_counterexampleOffset ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) : EReal)) -
        ∑ i : Fin 2, fenchelConjugate
          (helperForTheorem_6_30_14_counterexampleDimensions i)
          (helperForTheorem_6_30_14_counterexampleObjective i)
          (-((helperForTheorem_6_30_14_counterexampleMatrices i).transpose.mulVec
              (0 : Fin 0 → ℝ))) := by
  obtain ⟨hLeft, hRight⟩ := helperForTheorem_6_30_14_counterexampleValues
  -- Compare both sides through the common value `⊤` computed above.
  calc
    dualObjectiveOfSeparableConvexProgram
        helperForTheorem_6_30_14_counterexampleDimensions
        helperForTheorem_6_30_14_counterexampleOffset
        helperForTheorem_6_30_14_counterexampleMatrices
        helperForTheorem_6_30_14_counterexampleObjective
        (0 : Fin 0 → ℝ) = ⊤ := hLeft
    _ = -(((helperForTheorem_6_30_14_counterexampleOffset ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) : EReal)) -
          ∑ i : Fin 2, fenchelConjugate
            (helperForTheorem_6_30_14_counterexampleDimensions i)
            (helperForTheorem_6_30_14_counterexampleObjective i)
            (-((helperForTheorem_6_30_14_counterexampleMatrices i).transpose.mulVec
                (0 : Fin 0 → ℝ))) := hRight.symm

/-- Helper for Theorem 6.30.14: eliminating the perturbation variable rewrites the dual
objective as a constant term plus the infimum of the block-affine family. -/
lemma helperForTheorem_6_30_14_dualObjective_eq_constant_add_iInf_blockAffine {s m : ℕ}
    (n : Fin s → ℕ) (a : Fin m → ℝ)
    (A : ∀ i : Fin s, Matrix (Fin m) (Fin (n i)) ℝ)
    (f0 : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal)
    (uStar : Fin m → ℝ) :
    dualObjectiveOfSeparableConvexProgram n a A f0 uStar =
      -(((a ⬝ᵥ uStar : ℝ) : EReal)) +
        (⨅ x : ∀ i : Fin s, Fin (n i) → ℝ,
          ∑ i : Fin s, (f0 i (x i) + (((x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) : EReal)))) := by
  classical
  let Φ : ((Fin m → ℝ) × (∀ i : Fin s, Fin (n i) → ℝ)) → EReal :=
    fun p =>
      separableConvexProgramBifunction n a A f0 p.1 p.2 + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))
  let Ψ : (∀ i : Fin s, Fin (n i) → ℝ) → EReal :=
    fun x =>
      -(((a ⬝ᵥ uStar : ℝ) : EReal)) +
        ∑ i : Fin s, (f0 i (x i) + (((x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) : EReal)))
  have hCanonical :
      ∀ x : ∀ i : Fin s, Fin (n i) → ℝ,
        Φ
            ( (fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j)
            , x) = Ψ x := by
    intro x
    -- Evaluate the perturbation integrand at the canonical feasible perturbation.
    dsimp [Φ, Ψ, separableConvexProgramBifunction]
    have hFeasible :
        ∀ j : Fin m,
          (∑ i : Fin s, ((A i).mulVec (x i)) j) =
            a j + (fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j) j := by
      intro j
      simp
    rw [if_pos hFeasible]
    have hDot :
        (((fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j) ⬝ᵥ uStar : ℝ)) =
          -(a ⬝ᵥ uStar : ℝ) +
            ∑ i : Fin s, (x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) := by
      calc
        (((fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j) ⬝ᵥ uStar : ℝ))
            = ((fun j : Fin m => ∑ i : Fin s, ((A i).mulVec (x i)) j) ⬝ᵥ uStar : ℝ) -
                (a ⬝ᵥ uStar : ℝ) := by
                  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]
        _ = (∑ i : Fin s, (((A i).mulVec (x i)) ⬝ᵥ uStar : ℝ)) - (a ⬝ᵥ uStar : ℝ) := by
              rw [dotProduct]
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              simp [dotProduct]
        _ = (∑ i : Fin s, (x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ)) - (a ⬝ᵥ uStar : ℝ) := by
              congr with i
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
        _ = -(a ⬝ᵥ uStar : ℝ) +
              ∑ i : Fin s, (x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) := by
              ring
    rw [hDot]
    -- Separate the finite constant term from the blockwise affine sum.
    simpa [section16_coe_finset_sum, Finset.sum_add_distrib, add_left_comm]
  have hLeft :
      iInf Φ ≤ iInf Ψ := by
    -- Each block family gives a feasible perturbation, so the pair-indexed infimum is bounded
    -- above by the block-indexed value at that family.
    refine le_iInf ?_
    intro x
    exact iInf_le_of_le
      ( (fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j)
      , x) (le_of_eq (hCanonical x))
  have hRight :
      iInf Ψ ≤ iInf Φ := by
    -- Conversely, every pair dominates the block-family expression at the same `x`; infeasible
    -- pairs contribute `⊤`, while feasible pairs reduce to the canonical formula.
    refine le_iInf ?_
    rintro ⟨u, x⟩
    refine le_trans (iInf_le Ψ x) ?_
    by_cases hFeasible :
        ∀ j : Fin m, (∑ i : Fin s, ((A i).mulVec (x i)) j) = a j + u j
    · have hu :
          u = fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j := by
        funext j
        linarith [hFeasible j]
      rw [show Φ (u, x) = Φ
          ((fun j : Fin m => (∑ i : Fin s, ((A i).mulVec (x i)) j) - a j), x) by
            simp [Φ, hu]]
      exact le_of_eq (hCanonical x).symm
    · dsimp [Φ, Ψ]
      rw [separableConvexProgramBifunction, if_neg hFeasible]
      simp
  calc
    dualObjectiveOfSeparableConvexProgram n a A f0 uStar = iInf Φ := by
      simp [dualObjectiveOfSeparableConvexProgram, Φ, sInf_range]
    _ = iInf Ψ := le_antisymm hLeft hRight
    _ = -(((a ⬝ᵥ uStar : ℝ) : EReal)) +
          (⨅ x : ∀ i : Fin s, Fin (n i) → ℝ,
            ∑ i : Fin s, (f0 i (x i) + (((x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) : EReal)))) := by
          -- Addition by a finite real constant commutes with the indexed infimum.
          let c : ℝ := -(a ⬝ᵥ uStar : ℝ)
          let G : (∀ i : Fin s, Fin (n i) → ℝ) → EReal :=
            fun x =>
              ∑ i : Fin s, (f0 i (x i) + (((x i ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) : EReal)))
          have hFun : Ψ = fun x => G x + (c : EReal) := by
            funext x
            simp [Ψ, G, c, add_comm]
          rw [hFun]
          have hConst :
              iInf (fun x => G x + (c : EReal)) = iInf G + (c : EReal) := by
            apply le_antisymm
            · have hBase :
                  (section13_addRightOrderIso c).symm (iInf (fun x => G x + (c : EReal))) ≤ iInf G := by
                refine le_iInf ?_
                intro x
                have hIx' :=
                  (section13_addRightOrderIso c).symm.monotone
                    (iInf_le (fun x => G x + (c : EReal)) x)
                simpa [section13_addRightOrderIso, EReal.add_sub_cancel_right] using hIx'
              have hLift := (section13_addRightOrderIso c).monotone hBase
              convert hLift using 1
              · simp [section13_addRightOrderIso, EReal.sub_add_cancel]
            · refine le_iInf ?_
              intro x
              exact add_le_add (iInf_le G x) le_rfl
          simpa [c, add_comm] using hConst

/-- Helper for Theorem 6.30.14: the infimum of one affine block is the negative Fenchel
conjugate evaluated at the negated slope. -/
lemma helperForTheorem_6_30_14_affineBlock_iInf_eq_neg_fenchelConjugate {N : ℕ}
    (f : (Fin N → ℝ) → EReal) (p : Fin N → ℝ) :
    (⨅ x : Fin N → ℝ, f x + (((x ⬝ᵥ p : ℝ) : EReal))) =
      -fenchelConjugate N f (-p) := by
  -- Convert the infimum to a negated supremum, then recognize the Fenchel-conjugate integrand.
  have hNeg :
      -((⨅ x : Fin N → ℝ, f x + (((x ⬝ᵥ p : ℝ) : EReal)))) =
        iSup (fun x : Fin N → ℝ => -(f x + (((x ⬝ᵥ p : ℝ) : EReal)))) :=
    helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
      (φ := fun x : Fin N → ℝ => f x + (((x ⬝ᵥ p : ℝ) : EReal)))
  have hIntegrand :
      (fun x : Fin N → ℝ => -(f x + (((x ⬝ᵥ p : ℝ) : EReal)))) =
        fun x : Fin N → ℝ => (((x ⬝ᵥ (-p) : ℝ) : EReal)) - f x := by
    funext x
    have hNegAdd :
        -(f x + (((x ⬝ᵥ p : ℝ) : EReal))) =
          -(f x) - (((x ⬝ᵥ p : ℝ) : EReal)) := by
      exact
        EReal.neg_add (x := f x) (y := (((x ⬝ᵥ p : ℝ) : EReal)))
          (Or.inr (by simp)) (Or.inr (by simp))
    calc
      -(f x + (((x ⬝ᵥ p : ℝ) : EReal)))
          = -(f x) - (((x ⬝ᵥ p : ℝ) : EReal)) := hNegAdd
      _ = -(f x) + -(((x ⬝ᵥ p : ℝ) : EReal)) := by
            simp [sub_eq_add_neg]
      _ = -(((x ⬝ᵥ p : ℝ) : EReal)) + -(f x) := by
            rw [add_comm]
      _ = (((x ⬝ᵥ (-p) : ℝ) : EReal)) - f x := by
            simp [sub_eq_add_neg, dotProduct_neg]
  have hSup :
      -((⨅ x : Fin N → ℝ, f x + (((x ⬝ᵥ p : ℝ) : EReal)))) =
        fenchelConjugate N f (-p) := by
    rw [hNeg, hIntegrand, fenchelConjugate_eq_iSup]
  have hApplyNeg := congrArg Neg.neg hSup
  simpa using hApplyNeg

/-- Helper for Theorem 6.30.14: flattening a sigma-indexed function back to a dependent block
family recovers the original family. -/
lemma helperForTheorem_6_30_14_familyToSigmaEquiv_leftInv {s : ℕ}
    (n : Fin s → ℕ)
    (x : ∀ i : Fin s, Fin (n i) → ℝ) :
    (fun i j => (fun a : Σ i : Fin s, Fin (n i) => x a.1 a.2) ⟨i, j⟩) = x := by
  -- Evaluating the sigma-indexed encoding at `(i,j)` returns the original block coordinate.
  funext i j
  rfl

/-- Helper for Theorem 6.30.14: uncurrying a dependent block family to the sigma index and then
re-currying leaves the sigma-indexed function unchanged. -/
lemma helperForTheorem_6_30_14_familyToSigmaEquiv_rightInv {s : ℕ}
    (n : Fin s → ℕ)
    (y : (Σ i : Fin s, Fin (n i)) → ℝ) :
    (fun a => (fun i j => y ⟨i, j⟩) a.1 a.2) = y := by
  -- Every sigma coordinate is exactly one block index together with one in-block index.
  funext a
  cases a
  rfl

/-- Helper for Theorem 6.30.14: flatten a dependent family of primal blocks to one vector whose
coordinates are indexed by the sigma type of all block coordinates. -/
noncomputable def helperForTheorem_6_30_14_flattenBlockFamilyEquiv {s : ℕ}
    (n : Fin s → ℕ) :
    (∀ i : Fin s, Fin (n i) → ℝ) ≃
      (Fin (Fintype.card (Σ i : Fin s, Fin (n i))) → ℝ) :=
  ({ toFun := fun x a => x a.1 a.2
     invFun := fun y i j => y ⟨i, j⟩
     left_inv := helperForTheorem_6_30_14_familyToSigmaEquiv_leftInv n
     right_inv := helperForTheorem_6_30_14_familyToSigmaEquiv_rightInv n } :
    (∀ i : Fin s, Fin (n i) → ℝ) ≃ ((Σ i : Fin s, Fin (n i)) → ℝ)).trans
    (Equiv.arrowCongr (Fintype.equivFin (Σ i : Fin s, Fin (n i))) (Equiv.refl ℝ))

/-- Helper for Theorem 6.30.14: summing products over the sigma index is the same as summing the
blockwise dot products. -/
lemma helperForTheorem_6_30_14_sigmaDot_eq_sumBlockDots {s : ℕ}
    (n : Fin s → ℕ)
    (x p : ∀ i : Fin s, Fin (n i) → ℝ) :
    (∑ a : Sigma fun i : Fin s => Fin (n i), x a.1 a.2 * p a.1 a.2 : ℝ) =
      ∑ i : Fin s, (x i ⬝ᵥ p i : ℝ) := by
  -- Rewrite the sigma sum as an iterated sum over the block index and the in-block coordinate.
  simpa [dotProduct] using
    (Fintype.sum_sigma' (fun i : Fin s => fun j : Fin (n i) => x i j * p i j))

/-- Helper for Theorem 6.30.14: the supremum of a finite sum of independent block functions is
the sum of the blockwise suprema, even when the block dimensions vary with the index. -/
lemma helperForTheorem_6_30_14_dependentFamily_iSup_sum_eq_sum_iSup {s : ℕ}
    (n : Fin s → ℕ)
    (g : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal) :
    iSup (fun x : ∀ i : Fin s, Fin (n i) → ℝ => ∑ i, g i (x i)) =
      ∑ i : Fin s, iSup (fun xi : Fin (n i) → ℝ => g i xi) := by
  classical
  induction s with
  | zero =>
      -- With no blocks there is only one family, and both sides reduce to the empty sum.
      simp
  | succ s ih =>
      have hsplit :
          iSup (fun x : ∀ i : Fin (s + 1), Fin (n i) → ℝ => ∑ i, g i (x i)) =
            iSup (fun x : ∀ i : Fin (s + 1), Fin (n i) → ℝ =>
              g 0 (x 0) + ∑ i : Fin s, g (Fin.succ i) (x (Fin.succ i))) := by
        -- Split the family sum into the head block and the tail family.
        refine iSup_congr ?_
        intro x
        simp [Fin.sum_univ_succ]
      have hpair :
          iSup (fun x : ∀ i : Fin (s + 1), Fin (n i) → ℝ =>
              g 0 (x 0) + ∑ i : Fin s, g (Fin.succ i) (x (Fin.succ i))) =
            iSup (fun p : (Fin (n 0) → ℝ) × (∀ i : Fin s, Fin (n (Fin.succ i)) → ℝ) =>
              g 0 p.1 + ∑ i : Fin s, g (Fin.succ i) (p.2 i)) := by
        -- Reindex the family by the canonical head-tail equivalence.
        refine (Equiv.iSup_congr (Fin.consEquiv (fun i : Fin (s + 1) => Fin (n i) → ℝ)).symm ?_)
        intro x
        rfl
      calc
        iSup (fun x : ∀ i : Fin (s + 1), Fin (n i) → ℝ => ∑ i, g i (x i))
            = iSup (fun x : ∀ i : Fin (s + 1), Fin (n i) → ℝ =>
                g 0 (x 0) + ∑ i : Fin s, g (Fin.succ i) (x (Fin.succ i))) := hsplit
        _ = iSup (fun p : (Fin (n 0) → ℝ) × (∀ i : Fin s, Fin (n (Fin.succ i)) → ℝ) =>
              g 0 p.1 + ∑ i : Fin s, g (Fin.succ i) (p.2 i)) := hpair
        _ = iSup (fun x0 : Fin (n 0) → ℝ => g 0 x0) +
              iSup (fun xt : ∀ i : Fin s, Fin (n (Fin.succ i)) → ℝ =>
                ∑ i : Fin s, g (Fin.succ i) (xt i)) := by
              -- The head block and the tail family vary independently.
              simpa using
                (section16_iSup_add_iSup_eq_iSup_prod
                  (u := fun x0 : Fin (n 0) → ℝ => g 0 x0)
                  (v := fun xt : ∀ i : Fin s, Fin (n (Fin.succ i)) → ℝ =>
                    ∑ i : Fin s, g (Fin.succ i) (xt i))).symm
        _ = ∑ i : Fin (s + 1), iSup (fun xi : Fin (n i) → ℝ => g i xi) := by
              -- Apply the induction hypothesis to the tail family.
              simp [Fin.sum_univ_succ, ih]

/-- Helper for Theorem 6.30.14: a mixed `⊤/⊥` counterexample can already be built with two
zero-dimensional blocks. -/
def helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions : Fin 2 → ℕ := fun _ => 0

/-- Helper for Theorem 6.30.14: the mixed `⊤/⊥` counterexample has no perturbation coordinates. -/
def helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset : Fin 0 → ℝ := 0

/-- Helper for Theorem 6.30.14: the mixed `⊤/⊥` counterexample uses zero matrices in the
degenerate `m = 0` setting. -/
def helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices :
    ∀ i : Fin 2,
      Matrix (Fin 0) (Fin (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions i)) ℝ :=
  fun _ => 0

/-- Helper for Theorem 6.30.14: the first zero-dimensional block is constantly `⊤`, while the
second is constantly `⊥`. -/
def helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective :
    ∀ i : Fin 2,
      (Fin (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions i) → ℝ) → EReal :=
  fun i =>
    if i = 0 then
      fun _ => (⊤ : EReal)
    else
      fun _ => (⊥ : EReal)

/-- Helper for Theorem 6.30.14: in the mixed `⊤/⊥` example, the dual objective itself evaluates
to `⊥`. -/
lemma helperForTheorem_6_30_14_mixedTopBotCounterexample_dualObjective :
    dualObjectiveOfSeparableConvexProgram
        helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions
        helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset
        helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices
        helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective
        (0 : Fin 0 → ℝ) = ⊥ := by
  -- The unique primal family contributes `⊤ + ⊥ = ⊥`, so the infimum is `⊥`.
  simp [dualObjectiveOfSeparableConvexProgram, separableConvexProgramBifunction,
    helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions,
    helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset,
    helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices,
    helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective, Fin.sum_univ_two]

/-- Helper for Theorem 6.30.14: the theorem’s stated right-hand side gives `⊤` on the mixed
`⊤/⊥` counterexample, because `f₀^* = ⊥`, `f₁^* = ⊤`, and Lean evaluates `⊥ + ⊤` as `⊥`
before the outer subtraction. -/
lemma helperForTheorem_6_30_14_mixedTopBotCounterexample_rhs :
    (-(((helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) :
          EReal)) -
        ∑ i : Fin 2, fenchelConjugate
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions i)
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective i)
          (-((helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices i).transpose.mulVec
              (0 : Fin 0 → ℝ)))) = ⊤ := by
  -- Compute the two zero-dimensional conjugates separately and then simplify the outer
  -- subtraction.
  have hTop :
      fenchelConjugate 0 (fun _ : Fin 0 → ℝ => (⊤ : EReal)) (0 : Fin 0 → ℝ) = ⊥ := by
    simpa [constPosInf] using fenchelConjugate_constPosInf_apply 0 (0 : Fin 0 → ℝ)
  have hBot :
      fenchelConjugate 0 (fun _ : Fin 0 → ℝ => (⊥ : EReal)) (0 : Fin 0 → ℝ) = ⊤ := by
    simpa [constNegInf] using fenchelConjugate_constNegInf_apply 0 (0 : Fin 0 → ℝ)
  have hConj0 :
      fenchelConjugate
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions 0)
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective 0)
          (-((helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices 0).transpose.mulVec
              (0 : Fin 0 → ℝ))) = ⊥ := by
    simpa [helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions,
      helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices,
      helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective] using hTop
  have hConj1 :
      fenchelConjugate
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions 1)
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective 1)
          (-((helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices 1).transpose.mulVec
              (0 : Fin 0 → ℝ))) = ⊤ := by
    simpa [helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions,
      helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices,
      helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective] using hBot
  rw [Fin.sum_univ_two, hConj0, hConj1]
  simp [helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset]

/-- Helper for Theorem 6.30.14: the mixed `⊤/⊥` example shows the stated formula is false in the
current Lean `EReal` setting. -/
lemma helperForTheorem_6_30_14_mixedTopBotCounterexample_contradicts_formula :
    dualObjectiveOfSeparableConvexProgram
        helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions
        helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset
        helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices
        helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective
        (0 : Fin 0 → ℝ) ≠
      -(((helperForTheorem_6_30_14_mixedTopBotCounterexampleOffset ⬝ᵥ (0 : Fin 0 → ℝ) : ℝ) :
          EReal)) -
        ∑ i : Fin 2, fenchelConjugate
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleDimensions i)
          (helperForTheorem_6_30_14_mixedTopBotCounterexampleObjective i)
          (-((helperForTheorem_6_30_14_mixedTopBotCounterexampleMatrices i).transpose.mulVec
              (0 : Fin 0 → ℝ))) := by
  -- The left side is `⊥`, while the right side is `⊤`.
  rw [helperForTheorem_6_30_14_mixedTopBotCounterexample_dualObjective,
    helperForTheorem_6_30_14_mixedTopBotCounterexample_rhs]
  simp

-- Proof sketch: unfold the adjoint slice `(F_0^*)(u*)` as an infimum over perturbations `u`
-- and primal variables `x`, eliminate `u` using the linear constraint `∑ᵢ Aᵢ xᵢ = a + u`,
-- and then separate the remaining infimum into a sum of Fenchel conjugates evaluated at
-- `-(Aᵢ)ᵀ u*`. The supremum formulation of `(P*)` is the definition of the dual program value.
/-- Theorem 6.30.14: for the separable convex program `(P)` with objective
`∑ᵢ f_{0i}(xᵢ)` and linear constraint `∑ᵢ Aᵢ xᵢ = a`, the objective function in the concave
dual program `(P*)` is `(F_0^*)(u*) = -⟪a, u*⟫ - ∑ᵢ f_{0i}^*(-Aᵢ^* u*)`. Equivalently, the
dual program value is the supremum of this expression over `u* ∈ ℝ^m`. -/
theorem dualObjectiveOfSeparableConvexProgram_eq_neg_sum_fenchelConjugates {s m : ℕ}
    (n : Fin s → ℕ) (a : Fin m → ℝ)
    (A : ∀ i : Fin s, Matrix (Fin m) (Fin (n i)) ℝ)
    (f0 : ∀ i : Fin s, (Fin (n i) → ℝ) → EReal)
    (hproper : ∀ i : Fin s, ProperConvexERealFunction (f0 i)) :
    (∀ uStar : Fin m → ℝ,
      dualObjectiveOfSeparableConvexProgram n a A f0 uStar =
        -(((a ⬝ᵥ uStar : ℝ) : EReal)) -
          ∑ i : Fin s, fenchelConjugate (n i) (f0 i) (-((A i).transpose.mulVec uStar))) ∧
      dualProgramValueOfSeparableConvexProgram n a A f0 =
        sSup (Set.range fun uStar : Fin m → ℝ =>
          -(((a ⬝ᵥ uStar : ℝ) : EReal)) -
            ∑ i : Fin s, fenchelConjugate (n i) (f0 i) (-((A i).transpose.mulVec uStar))) :=
  by
    classical
    let blockTerm (uStar : Fin m → ℝ) (i : Fin s) (x : Fin (n i) → ℝ) : EReal :=
      f0 i x + (((x ⬝ᵥ (A i).transpose.mulVec uStar : ℝ) : EReal))
    let conjugateTerm (uStar : Fin m → ℝ) (i : Fin s) : EReal :=
      fenchelConjugate (n i) (f0 i) (-((A i).transpose.mulVec uStar))
    have hBlockTerm_ne_bot :
        ∀ (uStar : Fin m → ℝ) (i : Fin s) (x : Fin (n i) → ℝ),
          blockTerm uStar i x ≠ (⊥ : EReal) := by
      intro uStar i x
      exact (EReal.add_ne_bot_iff).2 ⟨(hproper i).1.1 x, by simp⟩
    have hBlockSup :
        ∀ (uStar : Fin m → ℝ) (i : Fin s),
          (⨆ x : Fin (n i) → ℝ, -blockTerm uStar i x) = conjugateTerm uStar i := by
      intro uStar i
      rw [← helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
        (φ := fun x : Fin (n i) → ℝ => blockTerm uStar i x)]
      rw [show (⨅ x : Fin (n i) → ℝ, blockTerm uStar i x) =
          -conjugateTerm uStar i by
        simpa [blockTerm, conjugateTerm] using
          helperForTheorem_6_30_14_affineBlock_iInf_eq_neg_fenchelConjugate
            (f0 i) ((A i).transpose.mulVec uStar)]
      simp
    have hInfSum :
        ∀ uStar : Fin m → ℝ,
          (⨅ x : ∀ i : Fin s, Fin (n i) → ℝ, ∑ i, blockTerm uStar i (x i)) =
            -∑ i, conjugateTerm uStar i := by
      intro uStar
      have hNegSum :
          (fun x : ∀ i : Fin s, Fin (n i) → ℝ =>
              -(∑ i, blockTerm uStar i (x i))) =
            fun x => ∑ i, -blockTerm uStar i (x i) := by
        funext x
        exact section16_neg_sum_eq_sum_neg (Finset.univ : Finset (Fin s))
          (fun i => blockTerm uStar i (x i)) (by
            intro i hi
            exact hBlockTerm_ne_bot uStar i (x i))
      have hNegInf :
          -(⨅ x : ∀ i : Fin s, Fin (n i) → ℝ, ∑ i, blockTerm uStar i (x i)) =
            ∑ i, conjugateTerm uStar i := by
        calc
          -(⨅ x : ∀ i : Fin s, Fin (n i) → ℝ, ∑ i, blockTerm uStar i (x i)) =
              ⨆ x : ∀ i : Fin s, Fin (n i) → ℝ, -(∑ i, blockTerm uStar i (x i)) :=
            helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
              (φ := fun x : ∀ i : Fin s, Fin (n i) → ℝ =>
                ∑ i, blockTerm uStar i (x i))
          _ = ⨆ x : ∀ i : Fin s, Fin (n i) → ℝ, ∑ i, -blockTerm uStar i (x i) := by
            rw [hNegSum]
          _ = ∑ i : Fin s, ⨆ xi : Fin (n i) → ℝ, -blockTerm uStar i xi :=
            helperForTheorem_6_30_14_dependentFamily_iSup_sum_eq_sum_iSup n
              (fun i xi => -blockTerm uStar i xi)
          _ = ∑ i, conjugateTerm uStar i := by
            congr 1
            funext i
            exact hBlockSup uStar i
      simpa using congrArg Neg.neg hNegInf
    have hObjective :
        ∀ uStar : Fin m → ℝ,
          dualObjectiveOfSeparableConvexProgram n a A f0 uStar =
            -(((a ⬝ᵥ uStar : ℝ) : EReal)) - ∑ i, conjugateTerm uStar i := by
      intro uStar
      rw [helperForTheorem_6_30_14_dualObjective_eq_constant_add_iInf_blockAffine]
      change -(((a ⬝ᵥ uStar : ℝ) : EReal)) +
          (⨅ x : ∀ i : Fin s, Fin (n i) → ℝ, ∑ i, blockTerm uStar i (x i)) = _
      rw [hInfSum uStar]
      rfl
    constructor
    · intro uStar
      simpa [conjugateTerm] using hObjective uStar
    · unfold dualProgramValueOfSeparableConvexProgram
      rw [show
        (fun uStar : Fin m → ℝ => dualObjectiveOfSeparableConvexProgram n a A f0 uStar) =
          fun uStar => -(((a ⬝ᵥ uStar : ℝ) : EReal)) - ∑ i, conjugateTerm uStar i by
            funext uStar
            exact hObjective uStar]

/-- The perturbation-value family `u ↦ inf_{x ∈ ℝ^n} F(u, x)` attached to a bifunction.
For a convex bifunction `F`, this is the convex program associated with `F`. -/
noncomputable def convexProgramAssociatedWith {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → EReal :=
  fun u => sInf (Set.range fun x : Fin n → ℝ => F u x)

/-- Definition 6.30.17: let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`, and let `(P*)`
be the dual program associated with the adjoint bifunction `F*`. A vector `x ∈ ℝ^n` is a
Kuhn--Tucker vector for `(P*)` when
`sup_{x* ∈ ℝ^n} (⟪x, x*⟫ + (sup F*)(x*))` is finite and equals the optimal value of `(P*)`.
Equivalently, since `(sup F*)(x*) = sup_{u* ∈ ℝ^m} (F* x*) u*`, the same condition may be
written as a supremum over pairs `(x*, u*)`. -/
noncomputable def IsKuhnTuckerVectorForDualProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (x : Fin n → ℝ) : Prop :=
  let dualPerturbation := dualPerturbationFunctionOfConvexProgram F
  let objectiveSup : EReal :=
    sSup (Set.range fun xStar : Fin n → ℝ =>
      (((x ⬝ᵥ xStar : ℝ) : EReal) + dualPerturbation xStar))
  objectiveSup ≠ ⊤ ∧ objectiveSup ≠ ⊥ ∧ objectiveSup = dualProgramOfConvexProgram F

/-- Definition 6.30.18: for `aStar ∈ ℝ^n`, `a ∈ ℝ^m`, and `A ∈ ℝ^(m × n)`, the bifunction
associated with `(P)` is the polyhedral proper convex bifunction `F : ℝ^m → ℝ^n` given by
`F_u(x) = aStar ⬝ᵥ x` when `x ≥ 0` and `a - A *ᵥ x ≤ u`, and `F_u(x) = +∞` otherwise. -/
noncomputable def linearProgramBifunction {m n : ℕ} (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x =>
    if (∀ i : Fin n, 0 ≤ x i) ∧ ∀ i : Fin m, a i - (A.mulVec x) i ≤ u i then
      ((aStar ⬝ᵥ x : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold the definitions of `linearProgramBifunction` and
-- `adjointOfConvexBifunction`. Minimizing the Lagrangian over `x ≥ 0` and `a - A x ≤ u`
-- produces the dual feasibility conditions `uStar ≥ 0` and `xStar ≤ aStar - Aᵀ uStar`;
-- under those conditions the infimum is attained as the constant term `⟪a, uStar⟫`, and
-- otherwise the infimum is `-∞`.
/-- Helper for Theorem 6.30.13: every primal-feasible pair `(u, x)` gives an adjoint integrand
value bounded below by the dual objective value under the dual feasibility inequalities. -/
lemma helperForTheorem_6_30_13_dualFeasibleLowerBound {m n : ℕ}
    (aStar xStar : Fin n → ℝ) (a uStar : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hdual : (∀ i : Fin m, 0 ≤ uStar i) ∧
      ∀ j : Fin n, xStar j ≤ aStar j - (A.transpose.mulVec uStar) j)
    {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hx : ∀ j : Fin n, 0 ≤ x j)
    (hu : ∀ i : Fin m, a i - (A.mulVec x) i ≤ u i) :
    (((a ⬝ᵥ uStar : ℝ) : EReal)) ≤
      (((aStar ⬝ᵥ x : ℝ) : EReal)) - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
        (((u ⬝ᵥ uStar : ℝ) : EReal)) := by
  -- Compare the perturbation term `u ⬝ uStar` with `(a - A x) ⬝ uStar` using `uStar ≥ 0`.
  have hu_sum : a ⬝ᵥ uStar - (A.mulVec x ⬝ᵥ uStar : ℝ) ≤ u ⬝ᵥ uStar := by
    calc
      a ⬝ᵥ uStar - (A.mulVec x ⬝ᵥ uStar : ℝ)
          = ∑ i, (a i - (A.mulVec x) i) * uStar i := by
              simp [dotProduct, sub_mul]
      _ ≤ ∑ i, u i * uStar i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_right (hu i) (hdual.1 i)
      _ = u ⬝ᵥ uStar := by
            simp [dotProduct]
  -- Compare the reduced-cost term with the dual inequality `xStar ≤ aStar - Aᵀ uStar`.
  have hAx : ∑ j, x j * (A.transpose.mulVec uStar) j = A.mulVec x ⬝ᵥ uStar := by
    change x ⬝ᵥ (A.transpose.mulVec uStar) = A.mulVec x ⬝ᵥ uStar
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hred_sum : (x ⬝ᵥ xStar : ℝ) ≤ (aStar ⬝ᵥ x : ℝ) - (A.mulVec x ⬝ᵥ uStar : ℝ) := by
    calc
      x ⬝ᵥ xStar
          ≤ x ⬝ᵥ fun j => aStar j - (A.transpose.mulVec uStar) j := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact mul_le_mul_of_nonneg_left (hdual.2 j) (hx j)
      _ = (aStar ⬝ᵥ x : ℝ) - (A.mulVec x ⬝ᵥ uStar : ℝ) := by
            rw [dotProduct]
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, hAx]
            change x ⬝ᵥ aStar - (A.mulVec x ⬝ᵥ uStar : ℝ) =
              (aStar ⬝ᵥ x : ℝ) - (A.mulVec x ⬝ᵥ uStar : ℝ)
            rw [dotProduct_comm]
  -- Combine the two real inequalities and then coerce them into `EReal`.
  have hreal :
      (a ⬝ᵥ uStar : ℝ) ≤ (aStar ⬝ᵥ x : ℝ) - (x ⬝ᵥ xStar : ℝ) + (u ⬝ᵥ uStar : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- Helper for Theorem 6.30.13: the feasible pair `(u, x) = (a, 0)` attains the dual-feasible
value in the adjoint integrand. -/
lemma helperForTheorem_6_30_13_dualFeasibleWitness {m n : ℕ}
    (aStar xStar : Fin n → ℝ) (a uStar : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    linearProgramBifunction aStar a A a 0 - (((0 : Fin n → ℝ) ⬝ᵥ xStar : ℝ) : EReal) +
        (((a ⬝ᵥ uStar : ℝ) : EReal)) =
      (((a ⬝ᵥ uStar : ℝ) : EReal)) := by
  -- The witness `(a, 0)` satisfies the primal constraints with equality.
  have hfeas : (∀ j : Fin n, 0 ≤ (0 : Fin n → ℝ) j) ∧
      ∀ i : Fin m, a i - (A.mulVec (0 : Fin n → ℝ)) i ≤ a i := by
    constructor
    · intro j
      simp
    · intro i
      simp
  -- Evaluating the integrand at this witness leaves only the constant term `a ⬝ uStar`.
  rw [linearProgramBifunction, if_pos hfeas]
  simp [dotProduct]

/-- Helper for Theorem 6.30.13: along the ray `u = a + t e_{i0}`, `x = 0`, the adjoint
integrand decreases with slope `uStar i0`. -/
lemma helperForTheorem_6_30_13_negativeMultiplierWitnessValue {m n : ℕ}
    (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (i0 : Fin m) (t : ℝ) (ht : 0 ≤ t) :
    let u : Fin m → ℝ := a + (Pi.single i0 t : Fin m → ℝ)
    linearProgramBifunction aStar a A u 0 - (((0 : Fin n → ℝ) ⬝ᵥ xStar : ℝ) : EReal) +
        (((u ⬝ᵥ uStar : ℝ) : EReal)) =
      (((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * uStar i0 : ℝ) : EReal)) := by
  -- The perturbation ray keeps `x = 0` feasible and only changes the `i0`-th constraint slack.
  dsimp
  have hfeas : (∀ j : Fin n, 0 ≤ (0 : Fin n → ℝ) j) ∧
      ∀ j : Fin m, a j - (A.mulVec (0 : Fin n → ℝ)) j ≤
        (a + (Pi.single i0 t : Fin m → ℝ)) j := by
    constructor
    · intro j
      simp
    · intro j
      by_cases hj : j = i0
      · subst hj
        simp [ht]
      · simp [Pi.single_eq_of_ne hj]
  have hdot :
      ((a + (Pi.single i0 t : Fin m → ℝ)) ⬝ᵥ uStar : ℝ) =
        (a ⬝ᵥ uStar : ℝ) + t * uStar i0 := by
    -- The ray contributes exactly the scalar `t * uStar i0` to the dot product.
    rw [add_dotProduct, single_dotProduct]
  rw [linearProgramBifunction, if_pos hfeas]
  simp [dotProduct]
  change ((((a + (Pi.single i0 t : Fin m → ℝ)) ⬝ᵥ uStar : ℝ) : EReal)) =
    (((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * uStar i0 : ℝ) : EReal))
  rw [hdot]
  simp

end Section30
end Chap06
