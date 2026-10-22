/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Lemma 6.3 lives in the finite simplex / entropy prox-geometry domain.

Sampled owner declarations:
* mathlib `stdSimplex`, via the Chapter 6 notation `Δ[n]`;
* mathlib `stdSimplex.barycenter` and `stdSimplex.barycenter_apply`, the canonical simplex center;
* project `entropyFunction` in `Chap02/Proposition_2_5`, the entropy owner on `Fin n → ℝ`;
* project `simplexL1Seminorm` and
  `entropyFunction_strongConvexOnWith_l1_stdSimplex` in `Chap02/Proposition_2_5`, the owner
  strong-convexity API on `Δ[n]`;
* project `EuclideanSpace.l1Seminorm` and
  `EuclideanSpace.entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex` in
  `Chap02/Proposition_2_5`, the Euclidean-coordinate bridge;
* project `normalizedEntropyProxFunction` in `Chap06/Definition_6_14`.

Best owner abstraction:
* source-facing: the three textbook entropy-prox facts of Lemma 6.3, evaluated at the simplex
  center `(1 / n) \bar e_n`;
* core/canonical: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view: the Euclidean-coordinate realization of the canonical simplex barycenter and the
  Euclidean pullback of the simplex owner theorem.

Primitive data:
* the positive dimension `n : ℕ+`;
* the canonical simplex barycenter `(stdSimplex.barycenter : Δ[n])`.

Derived API:
* the Euclidean-coordinate bridge `stdSimplexBarycenterEuclidean`;
* the simplex-owner strong-convexity theorem for the ambient normalized entropy formula on
  `Δ[n]`;
* the Euclidean-coordinate bridge theorem for that owner statement;
* the value-at-center and maximal-value statements for `normalizedEntropyProxFunction`.

Source/core/bridge triage:
* source-facing: the three entropy-prox statements from Lemma 6.3;
* core/canonical owners reused directly: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view kept here: `stdSimplexBarycenterEuclidean` and the Euclidean-coordinate transport of
  the simplex owner theorem.

The previous local duplicates `probabilitySimplex`, `simplexEntropyProxFunction`, and
`IsOneStronglyConvexOnProbabilitySimplex` have been deleted. Their mathematical content is already
owned canonically upstream by the simplex owner `Δ[n]`, the entropy owner `entropyFunction`, the
normalized entropy prox owner `normalizedEntropyProxFunction`, and the seminorm-based strong
convexity owner `StrongConvexOnWith`.
-/

/-- The Euclidean-coordinate realization of the canonical barycenter of `Δ_n`. -/
abbrev stdSimplexBarycenterEuclidean (n : ℕ+) : EuclideanSpace ℝ (Fin (n : ℕ)) :=
  (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ).symm (stdSimplex.barycenter : Δ[n])

/-- Helper for Lemma 6.3: adding a constant to a strongly convex function preserves the same
strong-convexity modulus on the same feasible set. -/
theorem strongConvexOnWith_const_add
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : Seminorm ℝ E} {μ : ℝ} {Q : Set E} {f : E → ℝ}
    (hf : StrongConvexOnWith p μ Q f) (c : ℝ) :
    StrongConvexOnWith p μ Q (fun x ↦ c + f x) := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Add the same constant to the owner inequality, then use `a + b = 1` to regroup the affine
  -- combination back into the shifted function values.
  calc
    c + f (a • x + b • y)
        ≤ c + (a • f x + b • f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ))) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left (hf.2.2 hx hy ha hb hab) c
    _ = a • (c + f x) + b • (c + f y) - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
      rw [smul_eq_mul, smul_eq_mul]
      calc
        c + (a * f x + b * f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)))
            = (a + b) * c + (a * f x + b * f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ))) := by
                rw [hab]
                ring
        _ = a * (c + f x) + b * (c + f y) - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
              ring

/-- Helper for Lemma 6.3: the entropy term at the simplex barycenter is `- log n`. -/
theorem entropyFunction_barycenter_eq_neg_log (n : ℕ+) :
    entropyFunction (n : ℕ) (stdSimplex.barycenter : Δ[n]) = -Real.log (n : ℝ) := by
  -- Expand the entropy sum, then rewrite every coordinate of the barycenter as `1 / n`.
  rw [entropyFunction_apply]
  have hbary : ∀ i : Fin (n : ℕ), (stdSimplex.barycenter : Δ[n]) i = (n : ℝ)⁻¹ := by
    intro i
    have hcoord :
        (stdSimplex.barycenter : Δ[n]) i = (Fintype.card (Fin (n : ℕ)) : ℝ)⁻¹ :=
      stdSimplex.barycenter_apply i
    simpa [Fintype.card_fin] using hcoord
  simp_rw [hbary]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  -- The constant sum reduces to `log ((n : ℝ)⁻¹)`, which is `- log n`.
  have hn_pos : 0 < (n : ℝ) := by
    positivity
  calc
    (n : ℝ) * ((n : ℝ)⁻¹ * Real.log ((n : ℝ)⁻¹))
        = ((n : ℝ) * (n : ℝ)⁻¹) * Real.log ((n : ℝ)⁻¹) := by ring
    _ = Real.log ((n : ℝ)⁻¹) := by
          simp [hn_pos.ne']
    _ = -Real.log (n : ℝ) := by
          rw [Real.log_inv]

/-- Helper for Lemma 6.3: the normalized entropy prox-function is bounded above by `log n` on the
standard simplex. -/
theorem normalizedEntropyProxFunction_le_log (n : ℕ+) (x : Δ[n]) :
    normalizedEntropyProxFunction n x ≤ Real.log (n : ℝ) := by
  -- After expanding the prox-function, each coordinate contribution is nonpositive on `[0, 1]`.
  rw [normalizedEntropyProxFunction_apply]
  have hsum_nonpos : ∑ i : Fin (n : ℕ), x i * Real.log (x i) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ ↦ ?_
    exact Real.mul_log_nonpos (stdSimplex.zero_le x i) (stdSimplex.le_one x i)
  linarith

/-- Helper for Lemma 6.3: the normalized entropy prox-function attains `log n` at every simplex
vertex. -/
theorem normalizedEntropyProxFunction_vertex_eq_log (n : ℕ+) (i : Fin (n : ℕ)) :
    normalizedEntropyProxFunction n (stdSimplex.vertex i) = Real.log (n : ℝ) := by
  -- At a simplex vertex all entropy terms vanish: the `i`-coordinate is `1 * log 1`, and every
  -- other coordinate is `0 * log 0`.
  rw [normalizedEntropyProxFunction_apply]
  simp [stdSimplex.vertex_coe, Pi.single_apply]

-- Proof sketch: Proposition 2.5 gives the owner strong-convexity statement for `entropyFunction`
-- on `Δ[n]`; adding the constant `log n` yields the ambient formula whose restriction to `Δ[n]`
-- is `normalizedEntropyProxFunction n`.
/-- Lemma 6.3 (1): on the simplex owner `Δ_n`, the ambient normalized entropy formula underlying
`normalizedEntropyProxFunction n` is `1`-strongly convex with respect to the canonical `ℓ₁`
seminorm. -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (simplexL1Seminorm (n : ℕ)) 1
      Δ[n]
      (fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x) := by
  -- Transport the known strong-convexity owner for `entropyFunction` through the harmless
  -- constant shift `f ↦ log n + f`.
  simpa using
    strongConvexOnWith_const_add
      (hf := entropyFunction_strongConvexOnWith_l1_stdSimplex (n := (n : ℕ)))
      (c := Real.log (n : ℝ))

-- Proof sketch: transport the simplex-owner strong-convexity statement along the coordinate
-- equivalence `EuclideanSpace.equiv (Fin n) ℝ`.
/-- Euclidean-coordinate bridge for Lemma 6.3 (1). -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_preimage_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (EuclideanSpace.l1Seminorm (n : ℕ)) 1
      ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n])
      (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) ↦
        Real.log (n : ℝ) +
          entropyFunction (n : ℕ) ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) x)) := by
  -- Apply the same constant-shift adapter to the Euclidean-coordinate owner theorem from
  -- Proposition 2.5.
  simpa using
    strongConvexOnWith_const_add
      (hf :=
        EuclideanSpace.entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex
          (n := (n : ℕ)))
      (c := Real.log (n : ℝ))

-- Proof sketch: evaluate the normalized entropy prox-function at the canonical simplex barycenter;
-- the entropy sum consists of `n` equal terms `(1 / n) * log (1 / n)`, and the added `log n`
-- cancels the total.
/-- Lemma 6.3 (2): the normalized entropy prox-function vanishes at the canonical barycenter
`(1 / n) \bar e_n` of `Δ_n`. -/
theorem normalizedEntropyProxFunction_barycenter_eq_zero (n : ℕ+) :
    normalizedEntropyProxFunction n (stdSimplex.barycenter : Δ[n]) = 0 := by
  -- Reduce the prox value to the already computed entropy value at the barycenter.
  rw [normalizedEntropyProxFunction, entropyFunction_barycenter_eq_neg_log]
  ring

-- Proof sketch: the entropy contribution is nonpositive on `Δ[n]`, so
-- `normalizedEntropyProxFunction n x ≤ log n` for all simplex points `x`; equality is attained at
-- any simplex vertex.
/-- Lemma 6.3 (3): the normalized entropy prox-function has maximal value `log n` on `Δ_n`. -/
theorem isGreatest_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    IsGreatest (Set.range (normalizedEntropyProxFunction n)) (Real.log (n : ℝ)) := by
  have hzero_lt : 0 < (n : ℕ) := n.pos
  let i : Fin (n : ℕ) := ⟨0, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · -- The maximum value is attained at a canonical simplex vertex.
    refine ⟨stdSimplex.vertex i, ?_⟩
    exact normalizedEntropyProxFunction_vertex_eq_log n i
  · -- Every point in the range comes from a simplex point where the entropy correction is
    -- nonpositive, so the value cannot exceed `log n`.
    rintro y ⟨x, rfl⟩
    exact normalizedEntropyProxFunction_le_log n x

/-- The supremum of the normalized entropy prox-function on `Δ_n` is `log n`. -/
theorem sSup_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    sSup (Set.range (normalizedEntropyProxFunction n)) = Real.log (n : ℝ) := by
  simpa using (isGreatest_range_normalizedEntropyProxFunction_eq_log n).csSup_eq
