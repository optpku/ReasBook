/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin

variable {n k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.3.1 lies in the Chapter 4 cubic hard-instance / degree-3 uniform-convexity
domain on Euclidean spaces.

Sampled owner-style declarations:
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter owner
  for feasible minimizer sets;
* `uniformConvexPowerModulus` in `Definition_4_2_8`, the chapter owner for the degree-`p` power
  modulus used on theorem surfaces;
* `HasUniformConvexityParameterOfDegree` in `Definition_4_2_11`, whose primitive witness data is
  a positive constant `σ` with `UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f`;
* `lower_bound_at_minimizer_of_uniformConvexOn` in `Theorem_4_2_1`, the chapter owner theorem
  built from `argmin[Q]` and `UniformConvexOn`;
* mathlib `UniformConvexOn.strictConvexOn`, the canonical bridge from a positive modulus witness
  to strict convexity.

Best owner abstraction:
* source-facing: the cubic hard-instance objective `fk hkn`, its explicit minimizer `x_*`, its
  optimal value, and the radius estimate;
* core/canonical: a positive degree-`3` witness
  `∃ σ > 0, UniformConvexOn Set.univ (uniformConvexPowerModulus σ (3 : ℝ)) (fk hkn)` together
  with the minimizer owner `argmin[Set.univ] (fk hkn)`;
* bridge/view: the singleton-argmin consequence for the explicit minimizer, plus the coordinate
  and norm-expansion lemmas below.

Primitive data:
* the hard-instance objective `fk hkn`;
* the explicit vector `cubicLowerBoundMinimizer n k`.

Derived API:
* the coordinate formula for the explicit minimizer;
* degree-`3` whole-space uniform convexity of `fk hkn`;
* uniqueness of the explicit global minimizer through the canonical owner
  `argmin[Set.univ] (fk hkn)`;
* the value and distance formulas at that minimizer.

The file therefore keeps the explicit minimizer as the source-facing owner for the hard instance,
but uses the chapter's canonical degree-`3` `UniformConvexOn` and `argmin[Set.univ]` surfaces
instead of a raw existential modulus function `∃ φ : ℝ → ℝ, ...` or a bespoke uniqueness package.
-/

/-- The explicit vector `x_*` with coordinates `x_*^(i) = (k - i + 1)_+`. -/
def cubicLowerBoundMinimizer (n k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i : Fin n ↦ ((k - (i : ℕ) : ℕ) : ℝ)

-- Proof sketch: unfold `cubicLowerBoundMinimizer`; on the `i`-th zero-based coordinate the value
-- is the truncated natural difference `k - i`, which is exactly `(k - i + 1)_+` in textbook
-- one-based indexing.
/-- The coordinates of the explicit minimizer are `x_*^(i) = (k - i + 1)_+`. -/
theorem cubicLowerBoundMinimizer_apply (i : Fin n) :
    cubicLowerBoundMinimizer n k i = ((k - (i : ℕ) : ℕ) : ℝ) := by
  simp [cubicLowerBoundMinimizer]

/-- Helper for Proposition 4 3 1: the positive-branch edge features are indexed by the
active differences, the terminal coordinate, and the inactive tail coordinates. -/
private abbrev PositiveBranchFeatureIndex (n k : ℕ) :=
  (Fin (k - 1)) ⊕ (Unit ⊕ Fin (n - k))

/-- Helper for Proposition 4 3 1: the edge feature is the adjacent difference
`x_i - x_{i+1}` on the active prefix. -/
private def positiveBranchEdge (hk : 0 < k) (hkn : k ≤ n) (x : E) (i : Fin (k - 1)) : ℝ :=
  x (Fin.castLE (by omega) (Fin.castSucc i)) - x (Fin.castLE (by omega) i.succ)

/-- Helper for Proposition 4 3 1: the terminal feature is the last active coordinate. -/
private def positiveBranchTerminal (hk : 0 < k) (hkn : k ≤ n) (x : E) : ℝ :=
  x (Fin.castLE (by omega) (Fin.last (k - 1)))

/-- Helper for Proposition 4 3 1: the tail features are the inactive coordinates starting at
index `k`. -/
private def positiveBranchTail (_ : k ≤ n) (x : E) (i : Fin (n - k)) : ℝ :=
  x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)

/-- Helper for Proposition 4 3 1: extend the active edge feature to natural indices by zero
outside `Finset.range (k - 1)`. -/
private def positiveBranchEdgeAtNat (hk : 0 < k) (hkn : k ≤ n) (x : E) (q : ℕ) : ℝ :=
  if hq : q < k - 1 then
    positiveBranchEdge (n := n) hk hkn x ⟨q, hq⟩
  else
    0

/-- Helper for Proposition 4 3 1: unify the positive-branch edge, terminal, and tail features
into one finite family of size `n`. -/
private def positiveBranchFeature
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    PositiveBranchFeatureIndex n k → ℝ
  | Sum.inl i => positiveBranchEdge (n := n) hk hkn x i
  | Sum.inr (Sum.inl _) => positiveBranchTerminal (n := n) hk hkn x
  | Sum.inr (Sum.inr i) => positiveBranchTail (n := n) hkn x i

/-- Helper for Proposition 4 3 1: the total absolute feature mass in the positive branch. -/
private def positiveBranchFeatureAbsSum (hk : 0 < k) (hkn : k ≤ n) (x : E) : ℝ :=
  ∑ j : PositiveBranchFeatureIndex n k, |positiveBranchFeature (n := n) hk hkn x j|

/-- Helper for Proposition 4 3 1: the positive-branch quadratic feature energy. -/
private def positiveBranchFeatureSqSum (hk : 0 < k) (hkn : k ≤ n) (x : E) : ℝ :=
  ∑ j : PositiveBranchFeatureIndex n k, |positiveBranchFeature (n := n) hk hkn x j| ^ (2 : ℕ)

/-- Helper for Proposition 4 3 1: the positive-branch cubic feature energy. -/
private def positiveBranchFeatureCubeSum (hk : 0 < k) (hkn : k ≤ n) (x : E) : ℝ :=
  ∑ j : PositiveBranchFeatureIndex n k, |positiveBranchFeature (n := n) hk hkn x j| ^ (3 : ℕ)

/-- Helper for Proposition 4 3 1: the bundled positive-branch cubic feature energy is
nonnegative. -/
private theorem positiveBranchFeatureCubeSum_nonneg
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    0 ≤ positiveBranchFeatureCubeSum (n := n) hk hkn x := by
  -- Every summand is a nonnegative cubic power of an absolute value.
  dsimp [positiveBranchFeatureCubeSum]
  exact Finset.sum_nonneg fun _ _ ↦ by positivity

/-- Helper for Proposition 4 3 1: the total absolute feature mass splits into edge, terminal, and
tail contributions. -/
private theorem positiveBranchFeatureAbsSum_eq
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    positiveBranchFeatureAbsSum (n := n) hk hkn x =
      (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn x i|) +
        |positiveBranchTerminal (n := n) hk hkn x| +
        ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn x i| := by
  -- Unfold the bundled sum once so later proofs can work with the three source feature families.
  simp [positiveBranchFeatureAbsSum, positiveBranchFeature, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4 3 1: the total cubic feature energy splits into edge, terminal, and
tail contributions. -/
private theorem positiveBranchFeatureCubeSum_eq
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    positiveBranchFeatureCubeSum (n := n) hk hkn x =
      (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn x i| ^ (3 : ℕ)) +
        |positiveBranchTerminal (n := n) hk hkn x| ^ (3 : ℕ) +
        ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn x i| ^ (3 : ℕ) := by
  -- Unfold the bundled cubic sum once so later proofs can rewrite to the source feature families.
  simp [positiveBranchFeatureCubeSum, positiveBranchFeature, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4 3 1: the active affine part is the sum of the edge features and the
terminal feature. -/
private def positiveBranchActiveLinearSum (hk : 0 < k) (hkn : k ≤ n) (x : E) : ℝ :=
  (∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn x i) +
    positiveBranchTerminal (n := n) hk hkn x

/-- Helper for Proposition 4 3 1: when the uniform-convexity degree is `3`, the canonical power
modulus is an ordinary cubic monomial. -/
private theorem uniformConvexPowerModulus_three
    (σ r : ℝ) :
    uniformConvexPowerModulus σ (3 : ℝ) r = (1 / 3 : ℝ) * σ * r ^ (3 : ℕ) := by
  simp [uniformConvexPowerModulus, mul_assoc]

/-- Helper for Proposition 4 3 1: a fixed explicit positive degree-three modulus small enough for
all finite-dimensional bridge estimates in this file. -/
private def cubicHardInstanceSigma (n : ℕ) : ℝ :=
  1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))

/-- Helper for Proposition 4 3 1: the one-dimensional cubic-minus-identity term is bounded below
by `-2 / 3`. -/
private theorem scalar_cubic_minus_id_ge (t : ℝ) :
    -((2 : ℝ) / 3) ≤ (1 / 3 : ℝ) * |t| ^ (3 : ℕ) - t := by
  -- Compare first with the even cubic in `|t|`, then factor the resulting polynomial.
  have hpoly_nonneg : 0 ≤ |t| ^ (3 : ℕ) - 3 * |t| + 2 := by
    have hfactor : |t| ^ (3 : ℕ) - 3 * |t| + 2 = (|t| - 1) ^ (2 : ℕ) * (|t| + 2) := by
      ring
    rw [hfactor]
    positivity
  have habs_bound : 0 ≤ (1 / 3 : ℝ) * |t| ^ (3 : ℕ) - |t| + 2 / 3 := by
    nlinarith
  have ht_le_abs : t ≤ |t| := le_abs_self t
  linarith

/-- Helper for Proposition 4 3 1: the pure scalar cubic is nonnegative. -/
private theorem scalar_cubic_nonneg (t : ℝ) :
    0 ≤ (1 / 3 : ℝ) * |t| ^ (3 : ℕ) := by
  positivity

/-- Helper for Proposition 4 3 1: adjacent differences along a finite chain telescope to the
initial value. -/
private theorem sum_range_sub_add (f : ℕ → ℝ) :
    ∀ m : ℕ, (∑ j ∈ Finset.range m, (f j - f (j + 1))) + f m = f 0
  | 0 => by simp
  | m + 1 => by
      -- Peel off the final adjacent difference and reduce to the shorter prefix chain.
      calc
        (∑ j ∈ Finset.range (m + 1), (f j - f (j + 1))) + f (m + 1)
            = ((∑ j ∈ Finset.range m, (f j - f (j + 1))) + f m) := by
                rw [Finset.sum_range_succ]
                ring
        _ = f 0 := sum_range_sub_add f m

/-- Helper for Proposition 4 3 1: the active prefix differences in `fk` telescope to the first
active coordinate. -/
private theorem prefix_adjacent_differences_telescope
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    (∑ i : Fin (k - 1),
        (x (Fin.castLE (by omega) (Fin.castSucc i)) -
          x (Fin.castLE (by omega) i.succ))) +
      x (Fin.castLE (by omega) (Fin.last (k - 1))) =
      x (Fin.castLE (by omega) (0 : Fin ((k - 1) + 1))) := by
  -- Convert the `Fin` chain into a `range` sum, then apply the elementary telescoping identity.
  let f : ℕ → ℝ := fun j ↦
    if hj : j < k then
      x ⟨j, lt_of_lt_of_le hj hkn⟩
    else
      0
  have hsum :
      (∑ i : Fin (k - 1),
          (x (Fin.castLE (by omega) (Fin.castSucc i)) -
            x (Fin.castLE (by omega) i.succ))) =
        ∑ j ∈ Finset.range (k - 1), (f j - f (j + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ f j - f (j + 1)) (k - 1)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt_k : (i : ℕ) < k := by
      omega
    have hi_succ_lt_k : (i : ℕ) + 1 < k := by
      omega
    have hcastSucc :
        (Fin.castLE (by omega) (Fin.castSucc i) : Fin n) =
          ⟨(i : ℕ), lt_of_lt_of_le hi_lt_k hkn⟩ := by
      ext
      simp
    have hsucc :
        (Fin.castLE (by omega) i.succ : Fin n) =
          ⟨(i : ℕ) + 1, lt_of_lt_of_le hi_succ_lt_k hkn⟩ := by
      ext
      simp
    rw [hcastSucc, hsucc]
    simp [f, hi_lt_k, hi_succ_lt_k]
  have hlast :
      x (Fin.castLE (by omega) (Fin.last (k - 1))) = f (k - 1) := by
    have hk_sub_lt_k : k - 1 < k := by
      omega
    have hlast_cast :
        (Fin.castLE (by omega) (Fin.last (k - 1)) : Fin n) =
          ⟨k - 1, lt_of_lt_of_le hk_sub_lt_k hkn⟩ := by
      ext
      simp
    rw [hlast_cast]
    simp [f, hk_sub_lt_k]
  have hzero :
      x (Fin.castLE (by omega) (0 : Fin ((k - 1) + 1))) = f 0 := by
    have hzero_cast :
        (Fin.castLE (by omega) (0 : Fin ((k - 1) + 1)) : Fin n) =
          ⟨0, lt_of_lt_of_le hk hkn⟩ := by
      ext
      simp
    rw [hzero_cast]
    simp [f, hk]
  rw [hsum, hlast, hzero]
  simpa using sum_range_sub_add f (k - 1)

/-- Helper for Proposition 4 3 1: in the positive branch, `fk` separates into the scalar
cubic-minus-identity features and the nonnegative cubic tail. -/
private theorem cubicLowerBoundObjective_eq_feature_sum_of_pos
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    fk hkn x =
      (∑ i : Fin (k - 1),
          ((1 / 3 : ℝ) *
              |x (Fin.castLE (by omega) (Fin.castSucc i)) -
                x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
            (x (Fin.castLE (by omega) (Fin.castSucc i)) -
              x (Fin.castLE (by omega) i.succ)))) +
        ((1 / 3 : ℝ) * |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ) -
          x (Fin.castLE (by omega) (Fin.last (k - 1)))) +
        (1 / 3 : ℝ) *
          ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
  -- Expand `fk`, telescope the linear term into the active chain, and regroup the scalar terms.
  -- Route correction: normalize the positive branch first, then replace the initial coordinate
  -- by the telescoping sum of edge differences and the terminal feature.
  have hfk :
      fk hkn x =
        (1 / 3 : ℝ) *
            ((∑ i : Fin (k - 1),
                |x (Fin.castLE (by omega) (Fin.castSucc i)) -
                    x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) +
              |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ)) -
          x (Fin.castLE (by omega) (0 : Fin ((k - 1) + 1))) +
          (1 / 3 : ℝ) *
            ∑ i : Fin (n - k),
              |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
    rw [fk_apply]
    simp [hk]
  have htel :
      x (Fin.castLE (by omega) (0 : Fin ((k - 1) + 1))) =
        (∑ i : Fin (k - 1),
            (x (Fin.castLE (by omega) i) -
              x (Fin.castLE (by omega) i.succ))) +
          x (Fin.castLE (by omega) (Fin.last (k - 1))) := by
    simpa only [Fin.castLE_castSucc] using
      (prefix_adjacent_differences_telescope (n := n) hk hkn x).symm
  let edgeCubeSum : ℝ :=
    ∑ i : Fin (k - 1),
      |x (Fin.castLE (by omega) (Fin.castSucc i)) -
          x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)
  let edgeDiffSum : ℝ :=
    ∑ i : Fin (k - 1),
      (x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ))
  let terminalCube : ℝ :=
    |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ)
  let terminalValue : ℝ :=
    x (Fin.castLE (by omega) (Fin.last (k - 1)))
  let tailCubeSum : ℝ :=
    ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ)
  calc
    fk hkn x =
        (1 / 3 : ℝ) * edgeCubeSum - edgeDiffSum +
          ((1 / 3 : ℝ) * terminalCube - terminalValue) +
          (1 / 3 : ℝ) * tailCubeSum := by
      rw [hfk, htel]
      dsimp [edgeCubeSum, edgeDiffSum, terminalCube, terminalValue, tailCubeSum]
      ring
    _ =
        (∑ i : Fin (k - 1),
            ((1 / 3 : ℝ) *
                |x (Fin.castLE (by omega) (Fin.castSucc i)) -
                    x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
              (x (Fin.castLE (by omega) (Fin.castSucc i)) -
                x (Fin.castLE (by omega) i.succ)))) +
          ((1 / 3 : ℝ) * |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ) -
            x (Fin.castLE (by omega) (Fin.last (k - 1)))) +
          (1 / 3 : ℝ) *
            ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
      dsimp [edgeCubeSum, edgeDiffSum, terminalCube, terminalValue, tailCubeSum]
      have hsplit :
          (∑ i : Fin (k - 1),
              ((1 / 3 : ℝ) *
                  |x (Fin.castLE (by omega) i) -
                      x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
                (x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)))) =
            (∑ i : Fin (k - 1),
                (1 / 3 : ℝ) *
                  |x (Fin.castLE (by omega) i) -
                      x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) -
              ((∑ i : Fin (k - 1), x (Fin.castLE (by omega) i)) -
                ∑ i : Fin (k - 1), x (Fin.castLE (by omega) i.succ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      have hcube :
          (1 / 3 : ℝ) *
            (∑ i : Fin (k - 1),
              |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) =
            ∑ i : Fin (k - 1),
              (1 / 3 : ℝ) *
                |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) := by
        rw [Finset.mul_sum]
      rw [hsplit]
      rw [hcube]
      simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Helper for Proposition 4 3 1: the bundled positive-branch feature index has cardinality `n`.
-/
private theorem positiveBranchFeatureIndex_card
    (hk : 0 < k) (hkn : k ≤ n) :
    Fintype.card (PositiveBranchFeatureIndex n k) = n := by
  have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk
  simp [PositiveBranchFeatureIndex]
  omega

/-- Helper for Proposition 4 3 1: the positive branch rewrites as the total cubic feature energy
minus the active affine feature sum. -/
private theorem cubicLowerBoundObjective_eq_cubicFeatureMinusLinear_of_pos
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    fk hkn x =
      (1 / 3 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn x -
        positiveBranchActiveLinearSum (n := n) hk hkn x := by
  -- Expand the bundled cubic and affine feature families once, then regroup the scalar terms.
  calc
    fk hkn x =
        (∑ i : Fin (k - 1),
            ((1 / 3 : ℝ) *
                |x (Fin.castLE (by omega) (Fin.castSucc i)) -
                    x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
              (x (Fin.castLE (by omega) (Fin.castSucc i)) -
                x (Fin.castLE (by omega) i.succ)))) +
          ((1 / 3 : ℝ) * |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ) -
            x (Fin.castLE (by omega) (Fin.last (k - 1)))) +
          (1 / 3 : ℝ) *
            ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
      exact cubicLowerBoundObjective_eq_feature_sum_of_pos (n := n) hk hkn x
    _ = (1 / 3 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn x -
          positiveBranchActiveLinearSum (n := n) hk hkn x := by
      rw [positiveBranchFeatureCubeSum_eq, positiveBranchActiveLinearSum]
      simp only [positiveBranchEdge, positiveBranchTerminal, positiveBranchTail,
        Fin.castLE_castSucc, one_div, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      ring_nf

/-- Helper for Proposition 4 3 1: the bundled positive-branch feature is linear in the ambient
vector argument. -/
private theorem positiveBranchFeature_add_smul
    (hk : 0 < k) (hkn : k ≤ n) (x y : E) (a b : ℝ)
    (j : PositiveBranchFeatureIndex n k) :
    positiveBranchFeature (n := n) hk hkn (a • x + b • y) j =
      a * positiveBranchFeature (n := n) hk hkn x j +
        b * positiveBranchFeature (n := n) hk hkn y j := by
  -- Each feature is an explicit coordinate difference or coordinate projection, so linearity is
  -- just coordinatewise algebra.
  cases j with
  | inl i =>
      simp [positiveBranchFeature, positiveBranchEdge, sub_eq_add_neg, mul_add, add_assoc,
        add_left_comm, add_comm]
  | inr j =>
      cases j with
      | inl u =>
          simp [positiveBranchFeature, positiveBranchTerminal]
      | inr i =>
          simp [positiveBranchFeature, positiveBranchTail]

/-- Helper for Proposition 4 3 1: the bundled positive-branch feature commutes with subtraction.
-/
private theorem positiveBranchFeature_sub
    (hk : 0 < k) (hkn : k ≤ n) (x y : E)
    (j : PositiveBranchFeatureIndex n k) :
    positiveBranchFeature (n := n) hk hkn (x - y) j =
      positiveBranchFeature (n := n) hk hkn x j -
        positiveBranchFeature (n := n) hk hkn y j := by
  simpa [sub_eq_add_neg] using
    positiveBranchFeature_add_smul (n := n) hk hkn x y (1 : ℝ) (-1 : ℝ) j

/-- Helper for Proposition 4 3 1: the active affine feature sum is linear. -/
-- TODO: split the edge sum and the terminal coordinate into separate linear identities before
-- reassembling the affine feature sum.
private theorem positiveBranchActiveLinearSum_add_smul
    (hk : 0 < k) (hkn : k ≤ n) (x y : E) (a b : ℝ) :
    positiveBranchActiveLinearSum (n := n) hk hkn (a • x + b • y) =
      a * positiveBranchActiveLinearSum (n := n) hk hkn x +
        b * positiveBranchActiveLinearSum (n := n) hk hkn y := by
  -- Rewrite the edge family coordinatewise, then add the terminal coordinate contribution.
  have hedge :
      ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn (a • x + b • y) i =
        a * ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn x i +
          b * ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn y i := by
    calc
      ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn (a • x + b • y) i =
          ∑ i : Fin (k - 1),
            (a * positiveBranchEdge (n := n) hk hkn x i +
              b * positiveBranchEdge (n := n) hk hkn y i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [positiveBranchEdge, sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm]
      _ =
          a * ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn x i +
            b * ∑ i : Fin (k - 1), positiveBranchEdge (n := n) hk hkn y i := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hterminal :
      positiveBranchTerminal (n := n) hk hkn (a • x + b • y) =
        a * positiveBranchTerminal (n := n) hk hkn x +
          b * positiveBranchTerminal (n := n) hk hkn y := by
    simp [positiveBranchTerminal]
  rw [positiveBranchActiveLinearSum, positiveBranchActiveLinearSum, positiveBranchActiveLinearSum,
    hedge, hterminal]
  ring

/-- Helper for Proposition 4 3 1: the real inner-product bilinear form is symmetric. -/
private theorem realInnerBilin_isSymm :
    (show LinearMap.BilinForm ℝ ℝ from innerₗ ℝ).IsSymm := by
  -- The scalar inner product is symmetric because real multiplication commutes.
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simpa using (real_inner_comm y x)

/-- Helper for Proposition 4 3 1: the real inner-product quadratic form is positive definite. -/
private theorem realInnerBilin_posDef :
    ((show LinearMap.BilinForm ℝ ℝ from innerₗ ℝ).toQuadraticMap).PosDef := by
  -- The associated quadratic form is `x ↦ ‖x‖²`, which is positive on nonzero scalars.
  intro x hx
  simpa [real_inner_self_eq_norm_sq] using sq_pos_iff.mpr (norm_ne_zero_iff.mpr hx)

/-- Helper for Proposition 4 3 1: on the primal space of the real inner product, the induced norm
is the usual absolute value. -/
private theorem realInnerPrimalSpace_norm_eq_abs
    (z : LinearMap.BilinForm.PrimalSpace (show LinearMap.BilinForm ℝ ℝ from innerₗ ℝ)) :
    ‖z‖ = |(z : ℝ)| := by
  simp

/-- Helper for Proposition 4 3 1: the scalar cubic `t ↦ (1 / 3) * |t|^3` is uniformly convex on
`ℝ` with modulus `r ↦ (1 / 6) * r^3`. -/
private theorem scalarCubic_uniformConvexOnHalf :
    UniformConvexOn Set.univ
      (uniformConvexPowerModulus (1 / 2 : ℝ) (3 : ℝ))
      (fun t : ℝ ↦ (1 / 3 : ℝ) * |t| ^ (3 : ℕ)) := by
  let B : LinearMap.BilinForm ℝ ℝ := show LinearMap.BilinForm ℝ ℝ from innerₗ ℝ
  have hPos : B.toQuadraticMap.PosDef := by
    simpa [B] using realInnerBilin_posDef
  letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
  have hthree : 2 ≤ (3 : ℝ) := by
    norm_num
  have hsigma : Real.rpow (1 / 2 : ℝ) ((3 : ℝ) - 2) = (1 / 2 : ℝ) := by
    norm_num
  have hpower :=
    powerFunction_uniformConvexOn (B := B) hPos (p := (3 : ℝ))
      (x0 := (0 : LinearMap.BilinForm.PrimalSpace B)) hthree
  have hfun (t : B.PrimalSpace) :
      powerFunction B (3 : ℝ) (0 : LinearMap.BilinForm.PrimalSpace B) t =
        (1 / 3 : ℝ) * |(t : ℝ)| ^ (3 : ℕ) := by
    -- Rewrite the intrinsic norm to the ambient absolute value before evaluating the power.
    have hpowerApply :
        powerFunction B (3 : ℝ) (0 : LinearMap.BilinForm.PrimalSpace B) t =
          (1 / 3 : ℝ) *
            Real.rpow
              (Real.sqrt ((B t) t))
              (3 : ℝ) := by
      simpa [sub_zero, LinearMap.BilinForm.primalSeminorm_apply] using
        (powerFunction_apply B (3 : ℝ) (0 : LinearMap.BilinForm.PrimalSpace B) t)
    have hroot : Real.sqrt ((B t) t) = |(t : ℝ)| := by
      change Real.sqrt (inner ℝ (t : ℝ) t) = |(t : ℝ)|
      simpa [real_inner_self_eq_norm_sq] using Real.sqrt_sq_eq_abs (t : ℝ)
    calc
      powerFunction B (3 : ℝ) (0 : LinearMap.BilinForm.PrimalSpace B) t =
          (1 / 3 : ℝ) *
            Real.rpow
              (Real.sqrt ((B t) t))
              (3 : ℝ) := hpowerApply
      _ = (1 / 3 : ℝ) * Real.rpow |(t : ℝ)| (3 : ℝ) := by
            rw [hroot]
      _ = (1 / 3 : ℝ) * |(t : ℝ)| ^ (3 : ℕ) := by
            norm_num [Real.rpow_natCast]
  refine ⟨by simpa using hpower.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (x : B.PrimalSpace) ∈ Set.univ := hx
  have hy' : (y : B.PrimalSpace) ∈ Set.univ := hy
  have hineq :=
    hpower.2
      (x := (x : B.PrimalSpace))
      hx'
      (y := (y : B.PrimalSpace))
      hy'
      ha hb hab
  have hmid :
      powerFunction B (3 : ℝ) (0 : LinearMap.BilinForm.PrimalSpace B) (a • x + b • y) =
        (1 / 3 : ℝ) * |a * x + b * y| ^ (3 : ℕ) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hfun (a • x + b • y)
  have hnorm_xy :
      Real.sqrt ((B x) x - (B x) y - ((B y) x - (B y) y)) = |x - y| := by
    have hquad :
        (B x) x - (B x) y - ((B y) x - (B y) y) = inner ℝ (x - y) (x - y) := by
      change inner ℝ x x - inner ℝ x y - (inner ℝ y x - inner ℝ y y) = inner ℝ (x - y) (x - y)
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
    have hself :
        inner ℝ (x - y) (x - y) = (x - y) ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]
      simp [Real.norm_eq_abs, sq]
    rw [hquad, hself]
    simpa [pow_two] using Real.sqrt_sq_eq_abs (x - y)
  have hnorm_xy_expanded :
      Real.sqrt ((B x) x + -(B x) y + ((B y) y + -(B y) x)) = |x - y| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm_xy
  have hsigma_expanded : (1 / 2 : ℝ).rpow ((3 : ℝ) + -2) = (1 / 2 : ℝ) := by
    norm_num
  have hineq' :
      (1 / 3 : ℝ) * |a * x + b * y| ^ (3 : ℕ) ≤
        a * ((1 / 3 : ℝ) * |x| ^ (3 : ℕ)) +
          b * ((1 / 3 : ℝ) * |y| ^ (3 : ℕ)) -
            a * b * uniformConvexPowerModulus (1 / 2 : ℝ) (3 : ℝ) ‖x - y‖ := by
    rw [hmid, hfun x, hfun y] at hineq
    norm_num at hineq
    simpa
      [hsigma, hsigma_expanded, hnorm_xy_expanded, Real.norm_eq_abs, smul_eq_mul,
        sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hineq
  -- Rewrite the intrinsic cubic power and its modulus back to the usual scalar absolute value.
  change (1 / 3 : ℝ) * |a * x + b * y| ^ (3 : ℕ) ≤
    a * ((1 / 3 : ℝ) * |x| ^ (3 : ℕ)) +
      b * ((1 / 3 : ℝ) * |y| ^ (3 : ℕ)) -
        a * b * uniformConvexPowerModulus (1 / 2 : ℝ) (3 : ℝ) ‖x - y‖
  exact hineq'

/-- Helper for Proposition 4 3 1: the scalar cubic obeys the midpoint inequality coming from the
uniform-convexity owner on `ℝ`. -/
private theorem scalar_cubic_midpoint_le
    {u v a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (1 / 3 : ℝ) * |a * u + b * v| ^ (3 : ℕ) ≤
      a * ((1 / 3 : ℝ) * |u| ^ (3 : ℕ)) +
        b * ((1 / 3 : ℝ) * |v| ^ (3 : ℕ)) -
          a * b * ((1 / 6 : ℝ) * |u - v| ^ (3 : ℕ)) := by
  have hmid :=
    scalarCubic_uniformConvexOnHalf.2
      (by simp : u ∈ (Set.univ : Set ℝ))
      (by simp : v ∈ (Set.univ : Set ℝ))
      ha hb hab
  have hmod :
      uniformConvexPowerModulus (1 / 2 : ℝ) (3 : ℝ) ‖u - v‖ =
        (((1 / 3 : ℝ) * (1 / 2 : ℝ)) * |u - v| ^ (3 : ℕ)) := by
    rw [uniformConvexPowerModulus_three]
    rw [Real.norm_eq_abs]
  have hmid' :
      (1 / 3 : ℝ) * |a * u + b * v| ^ (3 : ℕ) ≤
        a * ((1 / 3 : ℝ) * |u| ^ (3 : ℕ)) +
          b * ((1 / 3 : ℝ) * |v| ^ (3 : ℕ)) -
            a * b * ((((1 / 3 : ℝ) * (1 / 2 : ℝ)) * |u - v| ^ (3 : ℕ))) := by
    simpa [smul_eq_mul, hmod, Real.norm_eq_abs, sub_eq_add_neg, mul_assoc, mul_left_comm,
      mul_comm] using hmid
  -- Specialize the scalar owner directly at `u` and `v`.
  nlinarith

/-- Helper for Proposition 4 3 1: on nonnegative scalars, the degree-three midpoint inequality is
an explicit polynomial inequality once the remaining absolute value is reduced to `|x - y|`. -/
private theorem scalar_cubic_midpoint_le_nonneg
    {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (1 / 3 : ℝ) * (a * x + b * y) ^ (3 : ℕ) ≤
      a * ((1 / 3 : ℝ) * x ^ (3 : ℕ)) +
        b * ((1 / 3 : ℝ) * y ^ (3 : ℕ)) -
          a * b * ((1 / 6 : ℝ) * |x - y| ^ (3 : ℕ)) := by
  have hxy_nonneg : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  -- In the nonnegative branch, all absolute values collapse to the underlying scalars.
  simpa [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg hxy_nonneg] using
    scalar_cubic_midpoint_le (u := x) (v := y) ha hb hab

/-- Helper for Proposition 4 3 1: when the two scalars have opposite signs, the same degree-three
midpoint inequality is again a direct polynomial comparison after resolving the two absolute
values. -/
private theorem scalar_cubic_midpoint_le_opposite
    {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (1 / 3 : ℝ) * |a * x - b * y| ^ (3 : ℕ) ≤
      a * ((1 / 3 : ℝ) * x ^ (3 : ℕ)) +
        b * ((1 / 3 : ℝ) * y ^ (3 : ℕ)) -
          a * b * ((1 / 6 : ℝ) * |x + y| ^ (3 : ℕ)) := by
  -- Apply the general scalar inequality to `(x, -y)` and normalize the absolute values.
  simpa [sub_eq_add_neg, abs_of_nonneg hx, abs_of_nonneg hy, abs_neg, add_comm, add_left_comm] using
    scalar_cubic_midpoint_le (u := x) (v := -y) ha hb hab

/-- Helper for Proposition 4 3 1: a shifted adjacent-difference sum telescopes from `a` to `b`.
-/
private theorem sum_Ico_sub_add (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (Finset.sum (Finset.Ico a b) fun j ↦ (f j - f (j + 1))) + f b = f a := by
  -- Shift the interval back to a range sum and reuse the basic telescoping identity.
  let g : ℕ → ℝ := fun j ↦ f (a + j)
  have hshift :
      (∑ j ∈ Finset.Ico a b, (f j - f (j + 1))) =
        ∑ j ∈ Finset.range (b - a), (g j - g (j + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [g, Nat.add_assoc]
  have hb' : g (b - a) = f b := by
    simp [g, Nat.add_sub_of_le hab]
  have ha' : g 0 = f a := by
    simp [g]
  rw [hshift]
  simpa [hb', ha'] using sum_range_sub_add g (b - a)

/-- Helper for Proposition 4 3 1: on `ℝⁿ`, the Euclidean norm is bounded by the canonical
coordinate `ℓ₁` seminorm. -/
private theorem norm_le_l1Seminorm (v : E) :
    ‖v‖ ≤ EuclideanSpace.l1Seminorm n v := by
  -- Rewrite both norms by coordinates and compare `ℓ₂` with `ℓ₁`.
  rw [EuclideanSpace.norm_eq, EuclideanSpace.l1Seminorm_apply]
  refine (Real.sqrt_le_iff).2 ?_
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ norm_nonneg (v i)
  · simpa [sq] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin n ↦ ‖v i‖)
        (fun i _ ↦ norm_nonneg (v i))

/-- Helper for Proposition 4 3 1: every nonnegative finite family satisfies the coarse
`ℓ₁`-to-`ℓ₃` bound `(∑ aᵢ)^3 ≤ card(ι)^2 * ∑ aᵢ^3`. -/
private theorem sum_cube_le_card_sq_mul_sum_cubes
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) ^ (3 : ℕ) ≤ ((Fintype.card ι : ℝ) ^ (2 : ℕ)) * ∑ i, a i ^ (3 : ℕ) := by
  -- This is the degree-three specialization of the standard finite power-sum bound.
  simpa using
    (pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := a) (hf := fun i _ ↦ ha i) 2)

/-- Helper for Proposition 4 3 1: summing the scalar cubic midpoint inequality over the bundled
positive-branch feature family yields the featurewise cubic remainder term. -/
private theorem positiveBranchFeatureMidpointSum_le
    (hk : 0 < k) (hkn : k ≤ n) {x y : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (1 / 3 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn (a • x + b • y) ≤
      a * ((1 / 3 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn x) +
        b * ((1 / 3 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn y) -
          a * b * ((1 / 6 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn (x - y)) := by
  have hpoint :
      ∀ j : PositiveBranchFeatureIndex n k,
        (1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn (a • x + b • y) j| ^ (3 : ℕ) ≤
          a * ((1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn x j| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn y j| ^ (3 : ℕ)) -
              a * b * ((1 / 6 : ℝ) *
                |positiveBranchFeature (n := n) hk hkn (x - y) j| ^ (3 : ℕ)) := by
    intro j
    -- Apply the scalar cubic owner to each bundled feature coordinate.
    rw [positiveBranchFeature_add_smul (n := n) hk hkn x y a b j,
      positiveBranchFeature_sub (n := n) hk hkn x y j]
    simpa using
      scalar_cubic_midpoint_le
        (u := positiveBranchFeature (n := n) hk hkn x j)
        (v := positiveBranchFeature (n := n) hk hkn y j)
        ha hb hab
  have hsum :
      ∑ j : PositiveBranchFeatureIndex n k,
          (1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn (a • x + b • y) j| ^ (3 : ℕ) ≤
        ∑ j : PositiveBranchFeatureIndex n k,
          (a * ((1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn x j| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * |positiveBranchFeature (n := n) hk hkn y j| ^ (3 : ℕ)) -
              a * b * ((1 / 6 : ℝ) *
                |positiveBranchFeature (n := n) hk hkn (x - y) j| ^ (3 : ℕ))) := by
    exact Finset.sum_le_sum fun j _ ↦ hpoint j
  -- Expand both bundled feature sums once and factor the global scalars back out.
  simpa [positiveBranchFeatureCubeSum, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    using hsum

/-- Helper for Proposition 4 3 1: an active-prefix coordinate telescopes to the later edge
features plus the terminal feature. -/
private theorem activePrefixCoordinate_eq_intervalEdgeSum_add_terminal
    (hk : 0 < k) (hkn : k ≤ n) (h : E) {j : Fin n} (hj : (j : ℕ) < k) :
    h j =
      (∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
        positiveBranchEdgeAtNat (n := n) hk hkn h q) +
        positiveBranchTerminal (n := n) hk hkn h := by
  let f : ℕ → ℝ := fun q ↦ if hq : q < n then h ⟨q, hq⟩ else 0
  have hj_le : (j : ℕ) ≤ k - 1 := by
    omega
  have hsum :
      (∑ q ∈ Finset.Ico (j : ℕ) (k - 1), (f q - f (q + 1))) =
        ∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          positiveBranchEdgeAtNat (n := n) hk hkn h q := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq_left : q < k - 1 := (Finset.mem_Ico.mp hq).2
    have hq_mid : q + 1 < k := by
      omega
    have hq_lt_n : q < n := lt_of_lt_of_le (by omega) hkn
    have hq_succ_lt_n : q + 1 < n := lt_of_lt_of_le hq_mid hkn
    have hcastSucc :
        (Fin.castLE (by omega) (Fin.castSucc ⟨q, hq_left⟩) : Fin n) = ⟨q, hq_lt_n⟩ := by
      ext
      simp
    have hsucc :
        (Fin.castLE (by omega) (show Fin ((k - 1) + 1) from (⟨q, hq_left⟩ : Fin (k - 1)).succ) :
            Fin n) = ⟨q + 1, hq_succ_lt_n⟩ := by
      ext
      simp
    rw [positiveBranchEdgeAtNat]
    simp [hq_left, positiveBranchEdge, f, hq_lt_n, hq_succ_lt_n]
  have hterminal :
      f (k - 1) = positiveBranchTerminal (n := n) hk hkn h := by
    have hk_sub_lt_n : k - 1 < n := by
      omega
    have hlast :
        (Fin.castLE (by omega) (Fin.last (k - 1)) : Fin n) = ⟨k - 1, hk_sub_lt_n⟩ := by
      ext
      simp
    rw [positiveBranchTerminal, hlast]
    simp [f, hk_sub_lt_n]
  -- Rewrite the shifted telescoping identity in the positive-branch edge normal form.
  calc
    h j = f (j : ℕ) := by
      simp [f]
    _ =
        (∑ q ∈ Finset.Ico (j : ℕ) (k - 1), (f q - f (q + 1))) +
          f (k - 1) := by
            simpa using (sum_Ico_sub_add f hj_le).symm
    _ =
        (∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          positiveBranchEdgeAtNat (n := n) hk hkn h q) +
            positiveBranchTerminal (n := n) hk hkn h := by
              rw [hsum, hterminal]

/-- Helper for Proposition 4 3 1: every active-prefix coordinate is controlled by the absolute
sum of the edge features from that coordinate to the terminal coordinate. -/
private theorem prefixCoordinateAbsLeEdgeSumAddTerminalAbs
    (hk : 0 < k) (hkn : k ≤ n) (h : E) {j : Fin n} (hj : (j : ℕ) < k) :
    |h j| ≤
      (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
        |positiveBranchTerminal (n := n) hk hkn h| := by
  have hinterval :
      |∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          positiveBranchEdgeAtNat (n := n) hk hkn h q| ≤
        ∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          |positiveBranchEdgeAtNat (n := n) hk hkn h q| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hsubset :
      Finset.Ico (j : ℕ) (k - 1) ⊆ Finset.range (k - 1) := by
    intro q hq
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hq).2
  have hedges_le :
      (∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          |positiveBranchEdgeAtNat (n := n) hk hkn h q|) ≤
        ∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i| := by
    calc
      (∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          |positiveBranchEdgeAtNat (n := n) hk hkn h q|) ≤
          ∑ q ∈ Finset.range (k - 1),
            |positiveBranchEdgeAtNat (n := n) hk hkn h q| := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                (fun q _ _ ↦ abs_nonneg _)
      _ = ∑ i : Fin (k - 1), |positiveBranchEdgeAtNat (n := n) hk hkn h i| := by
            symm
            simpa using
              (Fin.sum_univ_eq_sum_range
                (fun q : ℕ ↦ |positiveBranchEdgeAtNat (n := n) hk hkn h q|)
                (k - 1))
      _ = ∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [positiveBranchEdgeAtNat]
  -- Route correction: use the stabilized interval telescoping equality, then bound the resulting
  -- interval sum by the full edge absolute-value sum.
  rw [activePrefixCoordinate_eq_intervalEdgeSum_add_terminal (n := n) hk hkn h hj]
  calc
    |(∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          positiveBranchEdgeAtNat (n := n) hk hkn h q) +
        positiveBranchTerminal (n := n) hk hkn h| ≤
      |∑ q ∈ Finset.Ico (j : ℕ) (k - 1),
          positiveBranchEdgeAtNat (n := n) hk hkn h q| +
        |positiveBranchTerminal (n := n) hk hkn h| := by
          exact abs_add_le _ _
    _ ≤
      (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
        |positiveBranchTerminal (n := n) hk hkn h| := by
          nlinarith [hinterval, hedges_le]

/-- Helper for Proposition 4 3 1: each inactive tail feature is exactly the corresponding ambient
coordinate. -/
private theorem positiveBranchTail_eq_coordinate
    (hkn : k ≤ n) (h : E) {j : Fin n} (hj : k ≤ (j : ℕ)) :
    positiveBranchTail (n := n) (k := k) hkn h ⟨(j : ℕ) - k, by omega⟩ = h j := by
  let i : Fin (n - k) := ⟨(j : ℕ) - k, by omega⟩
  have hi :
      (Fin.natAdd_castLEEmb (Nat.sub_le n k) i : Fin n) = j := by
    -- Compare the embedded tail index and `j` on their underlying natural numbers.
    ext
    simp [i, Fin.natAdd_castLEEmb]
    omega
  -- Rewrite the tail feature through the explicit embedding equality.
  simpa [positiveBranchTail, i] using congrArg h hi

/-- Helper for Proposition 4 3 1: every coordinate is controlled by the total absolute
positive-branch feature mass. -/
private theorem coordAbs_le_positiveBranchFeatureAbsSum
    (hk : 0 < k) (hkn : k ≤ n) (h : E) (j : Fin n) :
    |h j| ≤ positiveBranchFeatureAbsSum (n := n) hk hkn h := by
  by_cases hj : (j : ℕ) < k
  · have htail_nonneg :
        0 ≤ ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn h i| := by
      exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    rw [positiveBranchFeatureAbsSum_eq]
    calc
      |h j| ≤
          (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
            |positiveBranchTerminal (n := n) hk hkn h| := by
              exact prefixCoordinateAbsLeEdgeSumAddTerminalAbs (n := n) hk hkn h hj
      _ ≤
          (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
            |positiveBranchTerminal (n := n) hk hkn h| +
              ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn h i| := by
                nlinarith
  · have hj' : k ≤ (j : ℕ) := by
      omega
    let i : Fin (n - k) := ⟨(j : ℕ) - k, by omega⟩
    have hi :
        |positiveBranchTail (n := n) hkn h i| ≤
          ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn h i| := by
      simpa [i] using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin (n - k))))
          (f := fun i : Fin (n - k) ↦ |positiveBranchTail (n := n) hkn h i|)
          (by
            intro i _
            exact abs_nonneg _)
          (Finset.mem_univ i))
    have hprefix_nonneg :
        0 ≤
          (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
            |positiveBranchTerminal (n := n) hk hkn h| := by
      exact add_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)
        (abs_nonneg _)
    rw [positiveBranchFeatureAbsSum_eq]
    calc
      |h j| = |positiveBranchTail (n := n) hkn h i| := by
        rw [positiveBranchTail_eq_coordinate (n := n) (k := k) hkn h hj']
      _ ≤ ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn h i| := hi
      _ ≤
          (∑ i : Fin (k - 1), |positiveBranchEdge (n := n) hk hkn h i|) +
            |positiveBranchTerminal (n := n) hk hkn h| +
              ∑ i : Fin (n - k), |positiveBranchTail (n := n) hkn h i| := by
                nlinarith

/-- Helper for Proposition 4 3 1: summing the pointwise coordinate control yields a coarse
`ℓ₁` bound by the bundled positive-branch feature mass. -/
private theorem positiveBranchFeatureAbsSum_controls_l1
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    EuclideanSpace.l1Seminorm n h ≤
      (((n + 1 : ℕ) : ℝ)) * positiveBranchFeatureAbsSum (n := n) hk hkn h := by
  let A : ℝ := positiveBranchFeatureAbsSum (n := n) hk hkn h
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, positiveBranchFeatureAbsSum]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  -- Sum the coordinatewise bridge first, then relax the exact factor `n` to `n + 1`.
  rw [EuclideanSpace.l1Seminorm_apply]
  calc
    ∑ i : Fin n, |h i| ≤ ∑ i : Fin n, A := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [A] using coordAbs_le_positiveBranchFeatureAbsSum (n := n) (k := k) hk hkn h i
    _ = (n : ℝ) * A := by simp [A]
    _ ≤ (((n + 1 : ℕ) : ℝ)) * A := by
      have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ n
      exact mul_le_mul_of_nonneg_right hn_le hA_nonneg

/-- Helper for Proposition 4 3 1: the absolute positive-branch feature mass has cubic growth at
most quadratic in the ambient dimension. -/
-- TODO: finish this by combining `sum_cube_le_card_sq_mul_sum_cubes` with the exact cardinality
-- of `PositiveBranchFeatureIndex n k` after normalizing the remaining arithmetic side condition.
private theorem positiveBranchFeatureAbsSum_cube_le
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    positiveBranchFeatureAbsSum (n := n) hk hkn h ^ (3 : ℕ) ≤
      (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
  -- First apply the coarse `ℓ₁`-to-`ℓ₃` estimate on the bundled feature family, then relax the
  -- exact cardinality factor `n²` to `(n + 1)²`.
  have hsum :=
    sum_cube_le_card_sq_mul_sum_cubes
      (ι := PositiveBranchFeatureIndex n k)
      (fun j ↦ |positiveBranchFeature (n := n) hk hkn h j|)
      (fun j ↦ abs_nonneg _)
  rw [positiveBranchFeatureIndex_card (n := n) hk hkn] at hsum
  dsimp [positiveBranchFeatureAbsSum, positiveBranchFeatureCubeSum] at hsum
  have hcube_nonneg :
      0 ≤ positiveBranchFeatureCubeSum (n := n) hk hkn h := by
    dsimp [positiveBranchFeatureCubeSum]
    exact Finset.sum_nonneg fun j _ ↦ by positivity
  calc
    positiveBranchFeatureAbsSum (n := n) hk hkn h ^ (3 : ℕ) ≤
        ((n : ℝ) ^ (2 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := hsum
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
      have hfactor : ((n : ℝ) ^ (2 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        nlinarith [show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n]
      exact mul_le_mul_of_nonneg_right hfactor hcube_nonneg

/-- Helper for Proposition 4 3 1: the positive-branch cubic feature energy dominates the target
uniform-convexity modulus at `‖h‖`. -/
private theorem positiveBranchFeatureCubeDominatesNormCube
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖h‖ ≤
      (1 / 6 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
  let A : ℝ := positiveBranchFeatureAbsSum (n := n) hk hkn h
  have hnorm_cube :
      ‖h‖ ^ (3 : ℕ) ≤ (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) := by
    -- Raise the standard `ℓ₂ ≤ ℓ₁` comparison to the cubic power.
    gcongr
    exact norm_le_l1Seminorm (n := n) h
  have hl1_cube :
      (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) ≤ (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) * A ^ (3 : ℕ) := by
    have hbound := positiveBranchFeatureAbsSum_controls_l1 (n := n) (k := k) hk hkn h
    -- Cube the coarse `ℓ₁` estimate and normalize the scalar factor.
    calc
      (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) ≤ ((((n + 1 : ℕ) : ℝ) * A) ^ (3 : ℕ)) := by
            gcongr
      _ = (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) * A ^ (3 : ℕ) := by
            ring
  have hfeature_cube :
      A ^ (3 : ℕ) ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) *
        positiveBranchFeatureCubeSum (n := n) hk hkn h := by
    simpa [A] using positiveBranchFeatureAbsSum_cube_le (n := n) (k := k) hk hkn h
  have hfactor_nat :
      (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow2 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
      simpa using (one_le_pow₀ (n := 2) hone)
    calc
      (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) ≤
          (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
            nlinarith [show 0 ≤ (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) by positivity, hpow2]
      _ = (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
            rw [← pow_add]
  have hcube_nonneg :
      0 ≤ positiveBranchFeatureCubeSum (n := n) hk hkn h := by
    exact positiveBranchFeatureCubeSum_nonneg (n := n) hk hkn h
  have hcube :
      ‖h‖ ^ (3 : ℕ) ≤
        (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
    calc
      ‖h‖ ^ (3 : ℕ) ≤ (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) := hnorm_cube
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) * A ^ (3 : ℕ) := hl1_cube
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) *
            ((((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) *
              positiveBranchFeatureCubeSum (n := n) hk hkn h) := by
              exact mul_le_mul_of_nonneg_left hfeature_cube (by positivity)
      _ = (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
            rw [← mul_assoc, ← pow_add]
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
            exact mul_le_mul_of_nonneg_right hfactor_nat hcube_nonneg
  -- Rewrite the fixed modulus once and absorb the coarse dimension factor into the feature sum.
  rw [uniformConvexPowerModulus_three, cubicHardInstanceSigma]
  have hscale_nonneg : 0 ≤ (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hcube hscale_nonneg
  have hpow_ne : (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) ≠ 0 := by
    positivity
  calc
    (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) * ‖h‖ ^ (3 : ℕ) ≤
        (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) *
          ((((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * positiveBranchFeatureCubeSum (n := n) hk hkn h) :=
      hscaled
    _ = (1 / 6 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn h := by
      field_simp [hpow_ne]
      ring

/-- Helper for Proposition 4 3 1: in the degenerate branch `k = 0`, the coordinate cubic energy
already dominates the target uniform-convexity modulus. -/
private theorem coordinateCubeDominatesNormCube (h : E) :
    uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖h‖ ≤
      (1 / 6 : ℝ) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
  have hnorm_cube :
      ‖h‖ ^ (3 : ℕ) ≤ (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) := by
    -- Raise the standard `ℓ₂ ≤ ℓ₁` comparison to the cubic power.
    gcongr
    exact norm_le_l1Seminorm (n := n) h
  have hl1_cube :
      (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) ≤
        ((n : ℝ) ^ (2 : ℕ)) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
    -- Apply the coarse finite `ℓ₁`-to-`ℓ₃` estimate to the coordinate absolute values.
    rw [EuclideanSpace.l1Seminorm_apply]
    simpa [Real.norm_eq_abs] using
      sum_cube_le_card_sq_mul_sum_cubes (ι := Fin n) (fun i ↦ |h i|) (fun i ↦ abs_nonneg _)
  have hfactor_nat :
      (n : ℝ) ^ (2 : ℕ) ≤ (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
    have hpow2 :
        (n : ℝ) ^ (2 : ℕ) ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
      gcongr
      exact_mod_cast Nat.le_succ n
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow5 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) := by
      simpa using (one_le_pow₀ (n := 5) hone)
    calc
      (n : ℝ) ^ (2 : ℕ) ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := hpow2
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (5 : ℕ)) := by
            nlinarith [show 0 ≤ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) by positivity, hpow5]
      _ = (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
            rw [← pow_add]
  have hcoord_nonneg : 0 ≤ ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
    exact Finset.sum_nonneg fun i _ ↦ by positivity
  have hcube :
      ‖h‖ ^ (3 : ℕ) ≤
        (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
    calc
      ‖h‖ ^ (3 : ℕ) ≤ (EuclideanSpace.l1Seminorm n h) ^ (3 : ℕ) := hnorm_cube
      _ ≤ ((n : ℝ) ^ (2 : ℕ)) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := hl1_cube
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hfactor_nat hcoord_nonneg
  -- Rewrite the fixed modulus once and absorb the coarse dimension factor into the coordinate sum.
  rw [uniformConvexPowerModulus_three, cubicHardInstanceSigma]
  have hscale_nonneg : 0 ≤ (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hcube hscale_nonneg
  have hpow_ne : (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) ≠ 0 := by
    positivity
  calc
    (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) * ‖h‖ ^ (3 : ℕ) ≤
        (1 / 3 : ℝ) * (1 / (2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)))) *
          ((((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) * ∑ i : Fin n, |h i| ^ (3 : ℕ)) := hscaled
    _ = (1 / 6 : ℝ) * ∑ i : Fin n, |h i| ^ (3 : ℕ) := by
      field_simp [hpow_ne]
      ring

/-- Helper for Proposition 4 3 1: the global degree-three modulus chosen for this finite
dimensional hard instance is positive. -/
private theorem cubicHardInstanceSigma_pos :
    0 < cubicHardInstanceSigma n := by
  dsimp [cubicHardInstanceSigma]
  have hden : 0 < 2 * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
    positivity
  exact one_div_pos.mpr hden

/-- Helper for Proposition 4 3 1: every point lies above the explicit optimal value
`-(2 / 3) k`. -/
private theorem cubicLowerBoundObjective_ge_optimalValue
    (hkn : k ≤ n) (x : E) :
    -((2 : ℝ) / 3) * k ≤ fk hkn x := by
  by_cases hk : 0 < k
  · -- The source decomposition makes the lower bound a sum of scalar inequalities.
    rw [cubicLowerBoundObjective_eq_feature_sum_of_pos (n := n) hk hkn x]
    have hsum :
        ∑ i : Fin (k - 1), -((2 : ℝ) / 3) ≤
          ∑ i : Fin (k - 1),
            ((1 / 3 : ℝ) *
                |x (Fin.castLE (by omega) (Fin.castSucc i)) -
                  x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
              (x (Fin.castLE (by omega) (Fin.castSucc i)) -
                x (Fin.castLE (by omega) i.succ))) := by
      exact Finset.sum_le_sum fun i _ ↦ scalar_cubic_minus_id_ge _
    have htail_nonneg :
        0 ≤
          (1 / 3 : ℝ) *
            ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
      have hsum_nonneg :
          0 ≤ ∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ) := by
        exact Finset.sum_nonneg fun i _ ↦ by positivity
      positivity
    have hlast :
        -((2 : ℝ) / 3) ≤
          (1 / 3 : ℝ) * |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ) -
            x (Fin.castLE (by omega) (Fin.last (k - 1))) :=
      scalar_cubic_minus_id_ge _
    have hconst :
        ∑ i : Fin (k - 1), -((2 : ℝ) / 3) = -(((k - 1 : ℕ) : ℝ) * (2 / 3)) := by
      simp
    have hconst' :
        -(((k - 1 : ℕ) : ℝ) * (2 / 3)) = ((k - 1 : ℕ) : ℝ) * (-(2 : ℝ) / 3) := by
      ring
    rw [hconst, hconst'] at hsum
    have hk_nat : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
    have hk_real : ((k : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hk_nat.symm
    nlinarith
  · -- In the degenerate branch `k = 0`, `fk` is a pure nonnegative cubic sum.
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst hk0
    rw [fk_apply]
    simp only [Nat.lt_irrefl, ↓reduceDIte, one_div]
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| ^ (3 : ℕ) := by
      exact Finset.sum_nonneg fun i _ ↦ by positivity
    nlinarith

/-- Helper for Proposition 4 3 1: the explicit minimizer attains the value `-(2 / 3) k`. -/
private theorem cubicLowerBoundObjective_eq_optimalValue_at_minimizer
    (hkn : k ≤ n) :
    fk hkn (cubicLowerBoundMinimizer n k) = -((2 : ℝ) / 3) * k := by
  by_cases hk : 0 < k
  · -- Every active difference is `1`, the terminal coordinate is `1`, and the tail coordinates
    -- vanish.
    rw [cubicLowerBoundObjective_eq_feature_sum_of_pos (n := n) hk hkn
      (cubicLowerBoundMinimizer n k)]
    have hdiff :
        ∀ i : Fin (k - 1),
          cubicLowerBoundMinimizer n k (Fin.castLE (by omega) (Fin.castSucc i)) -
              cubicLowerBoundMinimizer n k (Fin.castLE (by omega) i.succ) = 1 := by
      intro i
      rw [cubicLowerBoundMinimizer_apply, cubicLowerBoundMinimizer_apply]
      have hstep : (k - (i : ℕ) : ℕ) = (k - ((i : ℕ) + 1) : ℕ) + 1 := by
        omega
      norm_num [hstep]
    have hlast :
        cubicLowerBoundMinimizer n k (Fin.castLE (by omega) (Fin.last (k - 1))) = 1 := by
      rw [cubicLowerBoundMinimizer_apply]
      have hlast_nat : (k - (k - 1) : ℕ) = 1 := by
        omega
      norm_num [hlast_nat]
    have htail :
        ∀ i : Fin (n - k),
          cubicLowerBoundMinimizer n k (Fin.natAdd_castLEEmb (Nat.sub_le n k) i) = 0 := by
      intro i
      have htail_cast :
          (Fin.natAdd_castLEEmb (Nat.sub_le n k) i : Fin n) =
            ⟨k + (i : ℕ), by omega⟩ := by
        ext
        simp [Fin.natAdd_castLEEmb]
        omega
      rw [htail_cast]
      rw [cubicLowerBoundMinimizer_apply]
      have htail_nat : (k - (k + (i : ℕ)) : ℕ) = 0 := by
        exact Nat.sub_eq_zero_of_le (by omega)
      simp [htail_nat]
    have hsum :
        (∑ i : Fin (k - 1),
            ((1 / 3 : ℝ) *
                |cubicLowerBoundMinimizer n k (Fin.castLE (by omega) (Fin.castSucc i)) -
                    cubicLowerBoundMinimizer n k (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) -
              (cubicLowerBoundMinimizer n k (Fin.castLE (by omega) (Fin.castSucc i)) -
                cubicLowerBoundMinimizer n k (Fin.castLE (by omega) i.succ)))) =
          ∑ i : Fin (k - 1), -((2 : ℝ) / 3) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hdiff i]
      norm_num
    have htail_sum :
        (1 / 3 : ℝ) *
          ∑ i : Fin (n - k),
            |cubicLowerBoundMinimizer n k (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^
              (3 : ℕ) = 0 := by
      rw [Finset.sum_eq_zero]
      · ring
      · intro i hi
        rw [htail i]
        norm_num
    rw [hsum, hlast, htail_sum]
    have hk_nat : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
    have hk_real : ((k : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hk_nat.symm
    simp
    nlinarith
  · -- The degenerate branch is the zero vector in the pure cubic objective.
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst hk0
    rw [fk_apply]
    simp [cubicLowerBoundMinimizer]

/-- Helper for Proposition 4 3 1: the Chapter 2 square-sum comparison is strict in `ℚ`. -/
private theorem sum_Icc_sq_lt_cubic_third_rat_local (m : ℕ) :
    (∑ i ∈ Finset.Icc 1 m, (i : ℚ) ^ (2 : ℕ)) <
      (((m + 1 : ℕ) : ℚ) ^ (3 : ℕ)) / 3 := by
  -- Expand the degree-two Faulhaber identity and compare the resulting cubic polynomial.
  rw [← Finset.Ico_add_one_right_eq_Icc 1 m]
  rw [sum_Ico_pow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two]
  have hm : (0 : ℚ) ≤ m := by
    positivity
  nlinarith

/-- Helper for Proposition 4 3 1: the Chapter 2 square-sum comparison is strict in `ℝ`. -/
private theorem sum_Icc_sq_lt_cubic_third_real_local (m : ℕ) :
    (∑ i ∈ Finset.Icc 1 m, (i : ℝ) ^ (2 : ℕ)) <
      (((m + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3 := by
  have hq := sum_Icc_sq_lt_cubic_third_rat_local m
  have hq' :
      ((∑ i ∈ Finset.Icc 1 m, (i : ℚ) ^ (2 : ℕ) : ℚ) : ℝ) <
        ((((m + 1 : ℕ) : ℚ) ^ (3 : ℕ) / 3 : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa using hq'

/-- Helper for Proposition 4 3 1: the truncated square sum over `range n` reindexes to the
one-based square sum over `Icc 1 k`. -/
private theorem sumRangeTruncatedNatSubSq_eq_sumIccSq
    (hkn : k ≤ n) :
    (∑ j ∈ Finset.range n, (((k - j : ℕ) : ℝ) ^ (2 : ℕ))) =
      ∑ i ∈ Finset.Icc 1 k, (i : ℝ) ^ (2 : ℕ) := by
  -- Split the ambient range at `k`, discard the zero tail, then reflect the surviving prefix to
  -- the one-based square sum.
  let f : ℕ → ℝ := fun j ↦ (((k - j : ℕ) : ℝ) ^ (2 : ℕ))
  rw [← Finset.sum_range_add_sum_Ico f hkn]
  have htail : (∑ j ∈ Finset.Ico k n, f j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hk_le_j : k ≤ j := (Finset.mem_Ico.mp hj).1
    have hsub : (k - j : ℕ) = 0 := Nat.sub_eq_zero_of_le hk_le_j
    simp [f, hsub]
  rw [htail, add_zero]
  have hrewrite :
      (∑ j ∈ Finset.range k, f j) =
        ∑ j ∈ Finset.range k, (((k - 1 - j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    have hnat : k - 1 - j + 1 = k - j := by
      omega
    simp [f, hnat]
  have hreflect :
      (∑ j ∈ Finset.range k, (((k - 1 - j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
        ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Finset.sum_range_reflect (fun j ↦ (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) k)
  rw [hrewrite, hreflect]
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by
    simpa using (Finset.Ico_succ_right_eq_Icc 1 k)]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring_nf

/-- Helper for Proposition 4 3 1: on the positive branch, the midpoint inequality can be stated
directly on the public objective `fk hkn`. -/
private theorem cubicLowerBoundObjective_midpoint_le_of_pos
    (hk : 0 < k) (hkn : k ≤ n) {x y : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    fk hkn (a • x + b • y) ≤
      a * fk hkn x + b * fk hkn y -
        a * b *
          uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ := by
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hfeature :=
    positiveBranchFeatureMidpointSum_le (n := n) (k := k) hk hkn (x := x) (y := y) ha hb hab
  have hlinear :=
    positiveBranchActiveLinearSum_add_smul (n := n) (k := k) hk hkn x y a b
  have hdom :=
    positiveBranchFeatureCubeDominatesNormCube (n := n) (k := k) hk hkn (x - y)
  have hdom' :
      a * b *
          uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ ≤
        a * b *
          ((1 / 6 : ℝ) * positiveBranchFeatureCubeSum (n := n) hk hkn (x - y)) := by
    exact mul_le_mul_of_nonneg_left hdom hab_nonneg
  -- Route correction: first rewrite the positive branch to the bundled feature surface, then use
  -- the already-closed feature midpoint and domination estimates.
  rw [cubicLowerBoundObjective_eq_cubicFeatureMinusLinear_of_pos (n := n) hk hkn (a • x + b • y),
    cubicLowerBoundObjective_eq_cubicFeatureMinusLinear_of_pos (n := n) hk hkn x,
    cubicLowerBoundObjective_eq_cubicFeatureMinusLinear_of_pos (n := n) hk hkn y, hlinear]
  nlinarith

/-- Helper for Proposition 4 3 1: when `k = 0`, the public objective is the pure coordinatewise
cubic sum, so the midpoint inequality is obtained by summing the scalar cubic owner. -/
private theorem cubicLowerBoundObjective_midpoint_le_of_zero
    (hk0 : k = 0) (hkn : k ≤ n) {x y : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    fk hkn (a • x + b • y) ≤
      a * fk hkn x + b * fk hkn y -
        a * b *
          uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ := by
  subst hk0
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hpoint :
      ∀ i : Fin n,
        (1 / 3 : ℝ) * |(a • x + b • y) i| ^ (3 : ℕ) ≤
          a * ((1 / 3 : ℝ) * |x i| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * |y i| ^ (3 : ℕ)) -
              a * b * ((1 / 6 : ℝ) * |(x - y) i| ^ (3 : ℕ)) := by
    intro i
    -- Each coordinate is exactly the scalar cubic midpoint inequality.
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      (scalar_cubic_midpoint_le (u := x i) (v := y i) ha hb hab)
  have hsum :
      ∑ i : Fin n, (1 / 3 : ℝ) * |(a • x + b • y) i| ^ (3 : ℕ) ≤
        ∑ i : Fin n,
          (a * ((1 / 3 : ℝ) * |x i| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * |y i| ^ (3 : ℕ)) -
              a * b * ((1 / 6 : ℝ) * |(x - y) i| ^ (3 : ℕ))) := by
    exact Finset.sum_le_sum fun i _ ↦ hpoint i
  have hsum' :
      (1 / 3 : ℝ) * ∑ i : Fin n, |(a • x + b • y) i| ^ (3 : ℕ) ≤
        a * ((1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ)) +
          b * ((1 / 3 : ℝ) * ∑ i : Fin n, |y i| ^ (3 : ℕ)) -
            a * b * ((1 / 6 : ℝ) * ∑ i : Fin n, |(x - y) i| ^ (3 : ℕ)) := by
    -- Pull the global weights back outside the coordinate sum once.
    simpa [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg,
      mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hdom := coordinateCubeDominatesNormCube (n := n) (x - y)
  have hdom' :
      a * b *
          uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ ≤
        a * b * ((1 / 6 : ℝ) * ∑ i : Fin n, |(x - y) i| ^ (3 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hdom hab_nonneg
  have hmain :
      (1 / 3 : ℝ) * ∑ i : Fin n, |(a • x + b • y) i| ^ (3 : ℕ) ≤
        a * ((1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ)) +
          b * ((1 / 3 : ℝ) * ∑ i : Fin n, |y i| ^ (3 : ℕ)) -
            a * b *
              uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ := by
    have hmod_sub :
        a * ((1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * ∑ i : Fin n, |y i| ^ (3 : ℕ)) -
              a * b * ((1 / 6 : ℝ) * ∑ i : Fin n, |(x - y) i| ^ (3 : ℕ)) ≤
          a * ((1 / 3 : ℝ) * ∑ i : Fin n, |x i| ^ (3 : ℕ)) +
            b * ((1 / 3 : ℝ) * ∑ i : Fin n, |y i| ^ (3 : ℕ)) -
              a * b *
                uniformConvexPowerModulus (cubicHardInstanceSigma n) (3 : ℝ) ‖x - y‖ := by
      nlinarith
    exact hsum'.trans hmod_sub
  -- Route correction: keep the degenerate branch in the coordinate normal form all the way to
  -- the final modulus absorption.
  simpa [fk_apply, Pi.smul_apply, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm,
    mul_comm] using hmain

-- Proof sketch: the cubic sum of adjacent differences and tail coordinates in `fk hkn`
-- yields a modulus witnessing uniform convexity.
/-- Uniform-convexity part of Proposition 4 3 1: the hard-instance objective `fk hkn` from
Definition 4.3.2 is uniformly convex. -/
theorem cubicLowerBoundObjective_uniformlyConvex
    (hkn : k ≤ n) :
    ∃ σ > 0,
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (3 : ℝ))
        (fk hkn) := by
  refine ⟨cubicHardInstanceSigma n, cubicHardInstanceSigma_pos (n := n), ?_⟩
  refine ⟨by simpa using (convex_univ : Convex ℝ (Set.univ : Set E)), ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases hk : 0 < k
  · -- Route correction: keep the positive branch on the public `fk` surface and reuse the
    -- packaged midpoint lemma instead of redoing the feature normalization here.
    simpa using
      cubicLowerBoundObjective_midpoint_le_of_pos
        (n := n) (k := k) hk hkn (x := x) (y := y) ha hb hab
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    -- The degenerate branch stays in the coordinate cubic normal form.
    simpa using
      cubicLowerBoundObjective_midpoint_le_of_zero
        (n := n) (k := k) hk0 hkn (x := x) (y := y) ha hb hab

-- Proof sketch: strict convexity follows from the positive modulus in
-- `cubicLowerBoundObjective_uniformlyConvex`, and a strictly convex function has at most one
-- global minimizer. The explicit vector `cubicLowerBoundMinimizer n k` is then identified as the
-- unique point of the canonical owner `argmin[Set.univ] (fk hkn)` by checking the optimality
-- conditions.
/-- Helper for Proposition 4 3 1: the degree-three power modulus is positive at every positive
radius. -/
private theorem uniformConvexPowerModulus_three_pos_of_pos
    {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    0 < uniformConvexPowerModulus σ (3 : ℝ) r := by
  -- Normalize the degree-three modulus, then use positivity of each scalar factor.
  rw [uniformConvexPowerModulus_three]
  positivity

/-- Helper for Proposition 4 3 1: the cubic hard-instance objective is strictly convex on the
whole space. -/
private theorem cubicLowerBoundObjective_strictConvexOn
    (hkn : k ≤ n) :
    StrictConvexOn ℝ Set.univ (fk hkn) := by
  rcases cubicLowerBoundObjective_uniformlyConvex (n := n) (k := k) hkn with
    ⟨σ, hσ, huniform⟩
  refine ⟨huniform.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hineq := huniform.2 hx hy ha.le hb.le hab
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hnorm_pos : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hmod_pos :
      0 < uniformConvexPowerModulus σ (3 : ℝ) ‖x - y‖ :=
    uniformConvexPowerModulus_three_pos_of_pos hσ hnorm_pos
  -- Positive weights and positive modulus turn the uniform-convexity drop into strict decrease.
  exact hineq.trans_lt (sub_lt_self _ (mul_pos hab_pos hmod_pos))

/-- Helper for Proposition 4 3 1: the explicit cubic hard-instance minimizer belongs to the
canonical argmin owner. -/
private theorem cubicLowerBoundMinimizer_mem_argmin
    (hkn : k ≤ n) :
    cubicLowerBoundMinimizer n k ∈ argmin[Set.univ] (fk hkn) := by
  refine mem_constrainedArgmin_iff.mpr ?_
  refine ⟨by simp, ?_⟩
  -- Rewrite the owner statement to the global pointwise lower bound already proved upstream.
  rw [isMinOn_univ_iff]
  intro x
  rw [cubicLowerBoundObjective_eq_optimalValue_at_minimizer (n := n) (k := k) hkn]
  exact cubicLowerBoundObjective_ge_optimalValue (n := n) (k := k) hkn x

/-- Proposition 4 3 1: the canonical minimizer set of the cubic hard-instance objective is the
singleton containing the explicit vector `x_*^(i) = (k - i + 1)_+`. -/
theorem cubicLowerBoundObjective_argmin_eq_singleton
    (hkn : k ≤ n) :
    argmin[Set.univ] (fk hkn) = {cubicLowerBoundMinimizer n k} := by
  -- Route correction: separate strict convexity and the explicit argmin witness before the final
  -- set-extensional uniqueness step.
  have hxStar_argmin :
      cubicLowerBoundMinimizer n k ∈ argmin[Set.univ] (fk hkn) :=
    cubicLowerBoundMinimizer_mem_argmin (n := n) (k := k) hkn
  have hstrict : StrictConvexOn ℝ Set.univ (fk hkn) :=
    cubicLowerBoundObjective_strictConvexOn (n := n) (k := k) hkn
  have hxStar_min : IsMinOn (fk hkn) Set.univ (cubicLowerBoundMinimizer n k) :=
    (mem_constrainedArgmin_iff.mp hxStar_argmin).2
  ext x
  constructor
  · intro hx
    rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
    have hx_eq :
        x = cubicLowerBoundMinimizer n k :=
      hstrict.eq_of_isMinOn hx_min hxStar_min hx_mem (by simp)
    simp [hx_eq]
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hxStar_argmin

-- Proof sketch: substitute the explicit coordinates of `cubicLowerBoundMinimizer` into the
-- defining formula of `fk hkn`; each adjacent difference contributes `1`,
-- the tail contributes the final `1`, and the linear term contributes `-k`.
/-- Evaluating the cubic hard instance at the explicit minimizer gives the optimal value
`f_k(x_*) = -(2 / 3) k`. -/
theorem cubicLowerBoundObjective_value_at_minimizer (hkn : k ≤ n) :
    fk hkn (cubicLowerBoundMinimizer n k) =
      -((2 : ℝ) / 3) * k := by
  -- Reuse the explicit feature evaluation at the minimizer.
  simpa using cubicLowerBoundObjective_eq_optimalValue_at_minimizer (n := n) (k := k) hkn

-- Proof sketch: the zero initialization leaves only the coordinates of `x_*`; summing their
-- squares gives `∑_{i=1}^k i^2` after reindexing from textbook one-based coordinates to `Fin n`,
-- using `k ≤ n` so the nonzero coordinates of `x_*` all lie in the ambient space.
/-- The squared Euclidean distance from the zero vector to the explicit minimizer is
`∑_{i=1}^k i^2` under the hard-instance range hypothesis `k ≤ n`. -/
theorem cubicLowerBoundMinimizer_sqDist_eq_sumSquares
    (hkn : k ≤ n) :
    ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) =
      ∑ i ∈ Finset.Icc 1 k, (i : ℝ) ^ (2 : ℕ) := by
  -- Normalize the Euclidean norm to a coordinate square sum, then invoke the arithmetic
  -- reindexing lemma for the truncated natural differences.
  let f : ℕ → ℝ := fun i ↦ (((k - i : ℕ) : ℝ) ^ (2 : ℕ))
  have hnorm :
      ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) = ∑ i ∈ Finset.range n, f i := by
    calc
      ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) =
          ∑ i : Fin n, (cubicLowerBoundMinimizer n k i) ^ (2 : ℕ) := by
            rw [sub_eq_add_neg, zero_add, norm_neg]
            simpa using (EuclideanSpace.real_norm_sq_eq (cubicLowerBoundMinimizer n k))
      _ = ∑ i : Fin n, f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [f, cubicLowerBoundMinimizer_apply]
      _ = ∑ i ∈ Finset.range n, f i := by
            simpa using (Fin.sum_univ_eq_sum_range f n)
  rw [hnorm, sumRangeTruncatedNatSubSq_eq_sumIccSq (n := n) (k := k) hkn]

-- Proof sketch: compare the sum of squares with the integral of `x^2` on `[0, k + 1]`, or use
-- the closed formula `k (k + 1) (2 k + 1) / 6`.
/-- The squared Euclidean distance from the zero vector to the explicit minimizer is strictly less
than `(k + 1)^3 / 3` under the hard-instance range hypothesis `k ≤ n`. -/
theorem cubicLowerBoundMinimizer_sqDist_lt
    (hkn : k ≤ n) :
    ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) <
      (((k + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3 := by
  -- Reduce the geometric norm to the Chapter 2 square-sum comparison.
  rw [cubicLowerBoundMinimizer_sqDist_eq_sumSquares (n := n) (k := k) hkn]
  exact sum_Icc_sq_lt_cubic_third_real_local k
