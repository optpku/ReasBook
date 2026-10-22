/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_14
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_16
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ₂" => (Set.preimage (WithLp.ofLp : E → Fin n → ℝ) Δ : Set E)

/- Text 9.6 is `source-facing`: it specializes mirror descent on the unit simplex to the negative
entropy potential and then records the resulting Kullback-Leibler Bregman geometry and
exponentiated-gradient update formula. The ambient mirror-map owner is the coordinatewise
negative entropy `negative_entropy_function` on the nonnegative orthant, while the simplex-side
minimization owners are `entropy_linear_objective` and `softmax_point`; this file uses the
matching Chapter 9 Bregman and mirror-descent formulas directly in that source-faithful setting.
-/

-- Proof sketch: unfold `entropy_linear_objective` and collect the linear term against
-- `fun i ↦ Real.log (x i) + 1 - t * g i`.
/-- Specializing `entropy_linear_objective` to the shifted log-weights
`i ↦ log (x_i) + 1 - t g_i` gives the explicit negative-entropy mirror-descent objective on the
simplex. -/
theorem entropy_linear_objective_log_add_one_sub_smul_apply
    (x g y : Fin n → ℝ) (t : ℝ) :
    entropy_linear_objective (fun i ↦ Real.log (x i) + 1 - t * g i) y =
      ∑ i, (t * g i - Real.log (x i) - 1) * y i + ∑ i, y i * Real.log (y i) := by
  -- Expand the entropy-linear objective and push the minus sign into the linear term.
  rw [entropy_linear_objective, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
  -- Each coordinate coefficient simplifies to the shifted log-weight form.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

-- Proof sketch: unfold `softmax_point`, rewrite `exp (log (x i) - t * g i)` as
-- `x i * exp (-t * g i)` using `hx_pos`, and simplify the common normalization factor.
/-- Evaluating the canonical softmax point of the shifted log-weights
`i ↦ log (x_i) - t g_i` gives the exponentiated-gradient coordinate formula. -/
theorem softmax_point_log_sub_smul_apply
    (x g : Fin n → ℝ) (t : ℝ) (hx_pos : ∀ i, 0 < x i) (i : Fin n) :
    softmax_point (fun j ↦ Real.log (x j) - t * g j) i =
      x i * Real.exp (-t * g i) / ∑ j, x j * Real.exp (-t * g j) := by
  -- Unfold the softmax coordinate and simplify the numerator first.
  calc
    softmax_point (fun j ↦ Real.log (x j) - t * g j) i
        = Real.exp (Real.log (x i) - t * g i) /
            ∑ j, Real.exp (Real.log (x j) - t * g j) := rfl
    _ = x i * Real.exp (-t * g i) /
          ∑ j, Real.exp (Real.log (x j) - t * g j) := by
          rw [show Real.log (x i) - t * g i = Real.log (x i) + (-t * g i) by ring,
            Real.exp_add, Real.exp_log (hx_pos i)]
    -- Then rewrite each denominator term in the same way.
    _ = x i * Real.exp (-t * g i) / ∑ j, x j * Real.exp (-t * g j) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [show Real.log (x j) - t * g j = Real.log (x j) + (-t * g j) by ring,
            Real.exp_add, Real.exp_log (hx_pos j)]

/-- Helper for Text 9.6: pairing the coordinate vector `WithLp.toLp 2 a` with `y` gives the
weighted coordinate sum `∑ i, a_i y_i`. -/
lemma inner_toLp_eq_sum_mul (a : Fin n → ℝ) (y : E) :
    inner ℝ (WithLp.toLp 2 a) y = ∑ i, a i * y i := by
  -- Rewrite the Euclidean inner product in coordinates and commute the scalar factors.
  simpa [dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp a y.ofLp)

/-- Helper for Text 9.6: the Euclidean Riesz map sends `WithLp.toLp 2 a` to the weighted sum of
the coordinate projections. -/
lemma toDual_toLp_eq_sum_proj (a : Fin n → ℝ) :
    (InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 a) =
      ∑ i, a i •
        (show E →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i) := by
  -- Compare the two linear functionals by evaluating both on an arbitrary vector.
  ext y
  calc
    ((InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 a)) y
        = inner ℝ (WithLp.toLp 2 a) y := by
            simp
    _ = ∑ i, a i * y i := inner_toLp_eq_sum_mul (a := a) (y := y)
    _ =
        (∑ i, a i •
          (show E →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)) y := by
          simp

/-- Helper for Text 9.6: coercing a finite real sum into `EReal` commutes with the finite sum. -/
private lemma ereal_coe_finset_sum (s : Finset (Fin n)) (r : Fin n → ℝ) :
    ((s.sum fun i ↦ r i : ℝ) : EReal) = s.sum fun i ↦ (((r i : ℝ)) : EReal) := by
  -- Induct on the finite index set so each step uses only `EReal.coe_add`.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi hs
    simp [Finset.sum_insert, hi, hs, EReal.coe_add]

/-- Helper for Text 9.6: on the nonnegative orthant, `negative_entropy_function n` is exactly the
`EReal` coercion of the finite real entropy sum `∑ i, x_i log x_i`. -/
lemma negativeEntropyFunction_eq_coe_sum_mul_log_of_nonneg
    (x : E) (hx_nonneg : ∀ i, 0 ≤ x i) :
    negative_entropy_function n x = (((∑ i, x i * Real.log (x i) : ℝ)) : EReal) := by
  -- First normalize each scalar branch to `x_i * log x_i`.
  rw [negative_entropy_function_apply]
  calc
    ∑ i, negative_entropy_scalar (x i) = ∑ i, (((x i * Real.log (x i) : ℝ)) : EReal) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [negative_entropy_scalar_of_nonneg (hx_nonneg i)]
    -- Then commute the finite sum with the `ℝ → EReal` coercion.
    _ = (((∑ i, x i * Real.log (x i) : ℝ)) : EReal) := by
      symm
      simpa using
        ereal_coe_finset_sum (s := (Finset.univ : Finset (Fin n)))
          (r := fun i ↦ x i * Real.log (x i))

/-- Helper for Text 9.6: if every coordinate of `x` is nonnegative, then the real-valued branch
of `negative_entropy_function n` is the usual entropy sum `∑ i, x_i log x_i`. -/
lemma negativeEntropyToReal_eq_sum_mul_log_of_nonneg
    (x : E) (hx_nonneg : ∀ i, 0 ≤ x i) :
    (negative_entropy_function n x).toReal = ∑ i, x i * Real.log (x i) := by
  -- Route correction: normalize the whole `EReal` owner before taking `toReal`.
  rw [negativeEntropyFunction_eq_coe_sum_mul_log_of_nonneg (x := x) hx_nonneg]
  simp

/-- Helper for Text 9.6: simplex points lie in the nonnegative orthant, so the coordinatewise
negative entropy has the standard real-valued formula there. -/
lemma negativeEntropyToReal_eq_sum_mul_log_of_memDelta₂
    (x : E) (hx : x ∈ Δ₂) :
    (negative_entropy_function n x).toReal = ∑ i, x i * Real.log (x i) := by
  -- A simplex point has nonnegative coordinates, so the branch formula applies directly.
  have hx_simplex : x.ofLp ∈ Δ := by
    exact hx
  refine negativeEntropyToReal_eq_sum_mul_log_of_nonneg (x := x) ?_
  intro i
  exact hx_simplex.1 i

/-- Helper for Text 9.6: at a positive scalar, the real-valued branch of
`negative_entropy_scalar` has derivative `log t + 1`. -/
lemma hasDerivAt_negativeEntropyScalar_toReal_of_pos
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (negative_entropy_scalar s).toReal) (Real.log t + 1) t := by
  -- Near a positive base point, the extended branch is literally `s ↦ s * log s`.
  have hEq :
      (fun s : ℝ ↦ (negative_entropy_scalar s).toReal) =ᶠ[nhds t]
        fun s ↦ s * Real.log s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [negative_entropy_scalar_of_nonneg (le_of_lt hs)]
    simpa using EReal.toReal_coe (s * Real.log s)
  exact (Real.hasDerivAt_mul_log ht.ne').congr_of_eventuallyEq hEq

/-- Helper for Text 9.6: a positive Euclidean simplex point has a neighborhood on which every
coordinate stays positive. -/
lemma eventually_pos_coords_of_pos
    (x : E) (hx_pos : ∀ i, 0 < x i) :
    ∀ᶠ z : E in nhds x, ∀ i : Fin n, 0 < z i := by
  -- Intersect the coordinatewise positive neighborhoods coming from continuity of each projection.
  have hall :
      ∀ᶠ z : E in nhds x, ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 < z i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hcont :
        ContinuousAt (fun z : E ↦ z i) x := by
      exact
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ) i).continuousAt
    exact
      (hcont.eventually (Ioi_mem_nhds (hx_pos i))).mono fun z hz ↦ hz
  simpa using hall

/-- Helper for Text 9.6: the clean entropy sum `z ↦ ∑ i, z_i log z_i` has the expected
Euclidean Fréchet derivative at a point with strictly positive coordinates. -/
lemma hasFDerivAt_entropySum_of_pos
    (x : E) (hx_pos : ∀ i, 0 < x i) :
    HasFDerivAt
      (fun z : E ↦ ∑ i, z i * Real.log (z i))
      ((InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 (fun i ↦ Real.log (x i) + 1))) x := by
  let proj : Fin n → E →L[ℝ] ℝ :=
    fun i ↦ (show E →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)
  have hsum :
      HasFDerivAt
        (fun z : E ↦ ∑ i, z i * Real.log (z i))
        (∑ i, (Real.log (x i) + 1) • proj i) x := by
    -- Differentiate each coordinate entropy term and sum the resulting linear maps.
    simpa [proj] using
      (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun i hi ↦ by
        have hcoord :
            HasFDerivAt (fun z : E ↦ z i)
              (show E →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i) x := by
          simpa using PiLp.hasFDerivAt_apply 2 x i
        have hscalar :
            HasDerivAt (fun s : ℝ ↦ s * Real.log s) (Real.log (x i) + 1) (x i) := by
          simpa using Real.hasDerivAt_mul_log (hx_pos i).ne'
        simpa [Function.comp, proj] using hscalar.comp_hasFDerivAt x hcoord)
  -- Finally rewrite the summed coordinate functional as the Riesz image of the gradient vector.
  simpa [proj, toDual_toLp_eq_sum_proj] using hsum

/-- Helper for Text 9.6: the Euclidean gradient of the real-valued branch of the coordinatewise
negative entropy has coordinates `log (x_i) + 1` at positive points. -/
lemma gradient_negativeEntropyToReal_apply
    (x : E) (hx_pos : ∀ i, 0 < x i) (i : Fin n) :
    ∇ (fun z : E ↦ (negative_entropy_function n z).toReal) x i = Real.log (x i) + 1 := by
  let entropySum : E → ℝ := fun z ↦ ∑ j, z j * Real.log (z j)
  have hsum :
      HasFDerivAt entropySum
        ((InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 (fun j ↦ Real.log (x j) + 1))) x :=
    hasFDerivAt_entropySum_of_pos (x := x) hx_pos
  have hEq :
      (fun z : E ↦ (negative_entropy_function n z).toReal) =ᶠ[nhds x] entropySum := by
    -- Near a strictly positive base point, the branched entropy owner equals the clean sum.
    filter_upwards [eventually_pos_coords_of_pos (x := x) hx_pos] with z hz
    have hz_nonneg : ∀ j, 0 ≤ z j := fun j ↦ le_of_lt (hz j)
    simpa [entropySum] using
      negativeEntropyToReal_eq_sum_mul_log_of_nonneg (x := z) hz_nonneg
  have hgrad :
      HasGradientAt
        (fun z : E ↦ (negative_entropy_function n z).toReal)
        (WithLp.toLp 2 (fun j ↦ Real.log (x j) + 1)) x := by
    -- Transfer the derivative across the eventual equality and read it as a gradient.
    simpa using (hsum.congr_of_eventuallyEq hEq).hasGradientAt
  -- Read off the `i`th coordinate of the gradient vector.
  simpa using congrArg (fun v : E ↦ v i) hgrad.gradient

/-- Helper for Text 9.6: the coordinatewise negative-entropy Bregman distance expands to the
entropy-gradient form before the simplex mass cancellation. -/
lemma negativeEntropyBregman_eq_entropyGradientForm
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    B[negative_entropy_function n] x y =
      (negative_entropy_function n x).toReal -
        (negative_entropy_function n y).toReal -
        ∑ i, (Real.log (y i) + 1) * (x i - y i) := by
  have hgrad :
      ∇ (fun z : E ↦ (negative_entropy_function n z).toReal) y =
        WithLp.toLp 2 (fun i ↦ Real.log (y i) + 1) := by
    ext i
    simpa using gradient_negativeEntropyToReal_apply (x := y) hy_pos i
  -- Unfold the Chapter 9 owner and rewrite the inner product in coordinates.
  rw [bregmanDistance_def, hgrad, inner_toLp_eq_sum_mul]
  simp

/-- Helper for Text 9.6: the entropy-gradient expression is the KL sum plus the simplex mass
correction `∑ i, y_i - ∑ i, x_i`. -/
lemma entropyGradientForm_eq_klPlusMassDifference
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    (negative_entropy_function n x).toReal -
      (negative_entropy_function n y).toReal -
      ∑ i, (Real.log (y i) + 1) * (x i - y i) =
      ∑ i, x i * Real.log (x i / y i) + (∑ i, y i) - (∑ i, x i) := by
  have hx_toReal := negativeEntropyToReal_eq_sum_mul_log_of_memDelta₂ (x := x) hx
  have hy_toReal := negativeEntropyToReal_eq_sum_mul_log_of_memDelta₂ (x := y) hy
  have hterm :
      ∀ i : Fin n,
        x i * Real.log (x i) -
            y i * Real.log (y i) -
            (Real.log (y i) + 1) * (x i - y i) =
          x i * Real.log (x i / y i) + y i - x i := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi]
      ring
    · rw [Real.log_div hxi (hy_pos i).ne']
      ring
  -- Expand the entropy branches and simplify each coordinate contribution.
  rw [hx_toReal, hy_toReal]
  calc
    ∑ i, x i * Real.log (x i) -
        ∑ i, y i * Real.log (y i) -
        ∑ i, (Real.log (y i) + 1) * (x i - y i)
      = ∑ i,
          (x i * Real.log (x i) -
            y i * Real.log (y i) -
            (Real.log (y i) + 1) * (x i - y i)) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ i, (x i * Real.log (x i / y i) + y i - x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
    _ = ∑ i, ((x i * Real.log (x i / y i) + y i) - x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ i, (x i * Real.log (x i / y i) + y i) - ∑ i, x i := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i, x i * Real.log (x i / y i) + (∑ i, y i) - (∑ i, x i) := by
          rw [Finset.sum_add_distrib]

-- Proof sketch: on simplex points `x` and `y`, rewrite the Chapter 9 mirror-descent objective
-- with `mirror_descent_update_objective_apply`, use the coordinatewise negative-entropy gradient
-- identity `∇ω(x)_i = log (x_i) + 1` at the strictly positive simplex point `x`, and simplify the
-- resulting expression to the Chapter 3 entropy-linear objective.
/-- On the simplex, the Chapter 9 mirror-descent objective for the coordinatewise negative-entropy
mirror map on the nonnegative orthant is the entropy-linear objective with shifted log-weights
`i ↦ log (x_i) + 1 - t g_i`. -/
theorem mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
    (x g y : E) (t : ℝ)
    (hx : x ∈ Δ₂) (hx_pos : ∀ i, 0 < x i) (hy : y ∈ Δ₂) :
    mirror_descent_update_objective
        (fun z : E ↦ (negative_entropy_function n z).toReal) x g t y =
      entropy_linear_objective (fun i ↦ Real.log (x i) + 1 - t * g i) y := by
  have hgrad :
      ∇ (fun z : E ↦ (negative_entropy_function n z).toReal) x =
        WithLp.toLp 2 (fun i ↦ Real.log (x i) + 1) := by
    ext i
    simpa using gradient_negativeEntropyToReal_apply (x := x) hx_pos i
  have hlinear :
      t • g - WithLp.toLp 2 (fun i ↦ Real.log (x i) + 1) =
        WithLp.toLp 2 (fun i ↦ t * g i - (Real.log (x i) + 1)) := by
    ext i
    simp [sub_eq_add_neg]
  -- Rewrite the mirror-descent objective into the coordinate entropy-linear owner.
  calc
    mirror_descent_update_objective
        (fun z : E ↦ (negative_entropy_function n z).toReal) x g t y
      = ∑ i, (t * g i - (Real.log (x i) + 1)) * y i +
          ∑ i, y i * Real.log (y i) := by
            rw [mirror_descent_update_objective_apply, hgrad, hlinear, inner_toLp_eq_sum_mul,
              negativeEntropyToReal_eq_sum_mul_log_of_memDelta₂ (x := y) hy]
    _ = ∑ i, (t * g i - Real.log (x i) - 1) * y i +
          ∑ i, y i * Real.log (y i) := by
            refine congrArg (fun r : ℝ => r + ∑ i, y i * Real.log (y i)) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = entropy_linear_objective (fun i ↦ Real.log (x i) + 1 - t * g i) y := by
          symm
          exact entropy_linear_objective_log_add_one_sub_smul_apply x g y t

-- Proof sketch: expand the Chapter 9 owner formula `B[negative_entropy_function n] x y`, use the
-- gradient identity `∇ω(y)_i = log (y_i) + 1` at the strictly positive simplex point `y`, and
-- then cancel the linear terms with the simplex identities `∑ i, x i = 1` and `∑ i, y i = 1`.
/-- The Chapter 9 Bregman distance of the coordinatewise negative entropy is the
Kullback-Leibler divergence on simplex points when the base point has strictly positive
coordinates. -/
theorem negative_entropy_bregman_eq_kullbackLeibler
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    B[negative_entropy_function n] x y =
      ∑ i, x i * Real.log (x i / y i) := by
  have hx_simplex : x.ofLp ∈ Δ := by
    exact hx
  have hy_simplex : y.ofLp ∈ Δ := by
    exact hy
  -- After the KL expansion, the simplex mass terms cancel to `0`.
  calc
    B[negative_entropy_function n] x y
      = (negative_entropy_function n x).toReal -
          (negative_entropy_function n y).toReal -
          ∑ i, (Real.log (y i) + 1) * (x i - y i) := by
            exact negativeEntropyBregman_eq_entropyGradientForm (x := x) (y := y) hx hy hy_pos
    _ = ∑ i, x i * Real.log (x i / y i) + (∑ i, y i) - (∑ i, x i) := by
          exact entropyGradientForm_eq_klPlusMassDifference (x := x) (y := y) hx hy hy_pos
    _ = ∑ i, x i * Real.log (x i / y i) := by
          rw [hy_simplex.2, hx_simplex.2]
          ring

-- Proof sketch: rewrite `B[negative_entropy_function n] x y` with the Chapter 9 defining formula,
-- use the negative-entropy gradient identity `∇ω(y)_i = log (y_i) + 1`, and simplify the
-- resulting linear term on the simplex.
/-- Expanding the coordinatewise negative-entropy Bregman distance on simplex points yields the
textbook entropy-gradient formula. -/
theorem negative_entropy_bregman_eq_kullbackLeibler_expanded
    (x y : E) (hx : x ∈ Δ₂) (hy : y ∈ Δ₂) (hy_pos : ∀ i, 0 < y i) :
    (negative_entropy_function n x).toReal -
      (negative_entropy_function n y).toReal -
      ∑ i, (Real.log (y i) + 1) * (x i - y i) =
      ∑ i, x i * Real.log (x i / y i) := by
  have hx_simplex : x.ofLp ∈ Δ := by
    exact hx
  have hy_simplex : y.ofLp ∈ Δ := by
    exact hy
  -- The expanded formula is the KL-plus-mass identity with the simplex masses canceled.
  calc
    (negative_entropy_function n x).toReal -
        (negative_entropy_function n y).toReal -
        ∑ i, (Real.log (y i) + 1) * (x i - y i)
      = ∑ i, x i * Real.log (x i / y i) + (∑ i, y i) - (∑ i, x i) := by
          exact entropyGradientForm_eq_klPlusMassDifference (x := x) (y := y) hx hy hy_pos
    _ = ∑ i, x i * Real.log (x i / y i) := by
          rw [hy_simplex.2, hx_simplex.2]
          ring

-- Proof sketch: first rewrite the simplex subproblem with
-- `mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective`. Then apply the
-- Chapter 3 softmax characterization of simplex minimizers and remove the irrelevant global
-- `+ 1` shift in the softmax weights, which does not change the normalized point. Because
-- `IsMinOn` does not encode feasibility, the simplex membership of `xNext` is kept explicit.
/-- Text 9.6: on the unit simplex, a feasible minimizer of the Chapter 9 mirror-descent subproblem
for the negative-entropy mirror map is the canonical softmax point of the shifted log-weights
`i ↦ log (x_i) - t g_i`, hence coordinatewise the exponentiated-gradient formula
`x_i^+ = x_i * exp (-t g_i) / ∑_j x_j * exp (-t g_j)`. -/
theorem mirror_descent_step_eq_exponentiated_gradient
    (x g xNext : E) (t : ℝ)
    (hx : x ∈ Δ₂) (hx_pos : ∀ i, 0 < x i) :
    xNext ∈ Δ₂ ∧
      IsMinOn
        (mirror_descent_update_objective
          (fun z : E ↦ (negative_entropy_function n z).toReal) x g t) Δ₂ xNext ↔
      xNext.ofLp = softmax_point (fun i ↦ Real.log (x i) - t * g i) := by
  have hx_simplex : x.ofLp ∈ Δ := by
    exact hx
  let yShift : Fin n → ℝ := fun i ↦ Real.log (x i) + 1 - t * g i
  let yBase : Fin n → ℝ := fun i ↦ Real.log (x i) - t * g i
  have hsoftmax_shift :
      softmax_point yShift = softmax_point yBase := by
    simpa [yShift, yBase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (softmax_point_add_const (y := yBase) (c := 1))
  constructor
  · rintro ⟨hxNext_mem, hmin⟩
    have hxNext_simplex : xNext.ofLp ∈ Δ := by
      exact hxNext_mem
    have hmin_linear :
        IsMinOn (entropy_linear_objective yShift) Δ xNext.ofLp := by
      rw [isMinOn_iff]
      intro z hz
      have hz_pre : WithLp.toLp 2 z ∈ Δ₂ := by
        change WithLp.ofLp (WithLp.toLp 2 z) ∈ Δ
        simpa using hz
      have hmin' := isMinOn_iff.mp hmin
      have hle := hmin' (WithLp.toLp 2 z) hz_pre
      -- Route correction: transport the minimizer statement through the normalized objective
      -- bridge instead of unfolding the mirror-descent owner again.
      have hxNext_obj :=
        mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
          (x := x) (g := g) (y := xNext) (t := t) hx hx_pos hxNext_mem
      have hz_obj :=
        mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
          (x := x) (g := g) (y := WithLp.toLp 2 z) (t := t) hx hx_pos hz_pre
      rw [hxNext_obj, hz_obj] at hle
      simpa [yShift] using hle
    have hsoft_shift :
        xNext.ofLp = softmax_point yShift :=
      eq_softmax_of_mem_stdSimplex_and_isMinOn_stdSimplex_entropyLinearObjective
        (y := yShift) (xstar := xNext.ofLp) hxNext_simplex hmin_linear
    exact hsoft_shift.trans hsoftmax_shift
  · intro hsoft
    letI : NeZero n := neZero_of_mem_stdSimplex hx_simplex
    have hsoft_shift :
        xNext.ofLp = softmax_point yShift := by
      calc
        xNext.ofLp = softmax_point yBase := hsoft
        _ = softmax_point yShift := hsoftmax_shift.symm
    have hxNext_simplex : xNext.ofLp ∈ Δ := by
      simpa [hsoft_shift] using softmax_point_mem_stdSimplex yShift
    have hxNext_mem : xNext ∈ Δ₂ := by
      exact hxNext_simplex
    have hmin_linear :
        IsMinOn (entropy_linear_objective yShift) Δ xNext.ofLp := by
      rw [isMinOn_iff]
      intro z hz
      have hle :
          entropy_linear_objective yShift (softmax_point yShift) ≤
            entropy_linear_objective yShift z :=
        entropyLinearObjective_softmax_le (y := yShift) (x := z) hz
      simpa [hsoft_shift] using hle
    have hmin_pre :
        IsMinOn
          (mirror_descent_update_objective
            (fun z : E ↦ (negative_entropy_function n z).toReal) x g t)
          Δ₂
          xNext := by
      rw [isMinOn_iff]
      intro z hz
      have hz_simplex : z.ofLp ∈ Δ := by
        exact hz
      have hle := (isMinOn_iff.mp hmin_linear) z.ofLp hz_simplex
      have hxNext_obj :=
        mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
          (x := x) (g := g) (y := xNext) (t := t) hx hx_pos hxNext_mem
      have hz_obj :=
        mirror_descent_update_objective_negative_entropy_eq_entropy_linear_objective
          (x := x) (g := g) (y := z) (t := t) hx hx_pos hz
      rw [hxNext_obj, hz_obj]
      simpa [yShift] using hle
    exact ⟨hxNext_mem, hmin_pre⟩

end
