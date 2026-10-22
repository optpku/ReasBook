/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part9

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- The coordinate-space action of the adjoint `A⋆` of a linear map `A : ℝ^n → ℝ^m`. -/
noncomputable def fenchelCoordinateAdjointApply {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (uStar : Fin m → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, (A (Pi.single i (1 : ℝ))) j * uStar j

/-- Helper for Lemma 31.0.8: the coordinate adjoint `fenchelCoordinateAdjointApply` is defined so
that the pairing term `∑ j, uStar j * (A x) j` can be rewritten as `∑ i, (A⋆ uStar) i * x i`. -/
lemma helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (∑ j, uStar j * (A x) j) = ∑ i, (fenchelCoordinateAdjointApply A uStar) i * x i := by
  classical
  -- Expand `x` on the standard basis `Pi.single i 1` and use linearity of `A`.
  have hbasis (i : Fin n) :
      (fun j : Fin n => if i = j then (1 : ℝ) else 0) = Pi.single i (1 : ℝ) := by
    funext j
    by_cases h : i = j
    · subst h
      simp [Pi.single_apply]
    · have h' : j ≠ i := by
        intro hj
        exact h hj.symm
      simp [Pi.single_apply, h, h']
  have hAx :
      A x = ∑ i : Fin n, x i • A (Pi.single i (1 : ℝ)) := by
    -- `LinearMap.pi_apply_eq_sum_univ` gives the standard-basis expansion using `if i = j`.
    simpa [hbasis] using (LinearMap.pi_apply_eq_sum_univ (f := A) x)
  have hAx_coord (j : Fin m) :
      (A x) j = ∑ i : Fin n, x i * (A (Pi.single i (1 : ℝ))) j := by
    -- Evaluate the basis expansion at coordinate `j` and simplify scalar multiplication.
    have h := congrArg (fun y : Fin m → ℝ => y j) hAx
    simpa [Finset.sum_apply, smul_eq_mul] using h
  -- Rewrite the left-hand side using the coordinate expansion and swap the finite sums.
  calc
    (∑ j, uStar j * (A x) j)
        = ∑ j, uStar j * ∑ i : Fin n, x i * (A (Pi.single i (1 : ℝ))) j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [hAx_coord]
    _ = ∑ j, ∑ i : Fin n, uStar j * (x i * (A (Pi.single i (1 : ℝ))) j) := by
          simp [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j, uStar j * (x i * (A (Pi.single i (1 : ℝ))) j) := by
          -- Avoid `simp` recursion: this is exactly `Finset.sum_comm`.
          exact Finset.sum_comm
    _ = ∑ i : Fin n, x i * ∑ j, (A (Pi.single i (1 : ℝ))) j * uStar j := by
          refine Finset.sum_congr rfl ?_
          intro i _
          -- Pull the scalar `x i` out of the inner sum and commute the factors into the
          -- `fenchelCoordinateAdjointApply` order.
          calc
            (∑ j, uStar j * (x i * (A (Pi.single i (1 : ℝ))) j))
                = ∑ j, x i * (uStar j * (A (Pi.single i (1 : ℝ))) j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j _
                    ring
            _ = x i * ∑ j, uStar j * (A (Pi.single i (1 : ℝ))) j := by
                  simpa [Finset.mul_sum]
            _ = x i * ∑ j, (A (Pi.single i (1 : ℝ))) j * uStar j := by
                  refine congrArg (fun t => x i * t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  ring
    _ = ∑ i : Fin n, (fenchelCoordinateAdjointApply A uStar) i * x i := by
          -- Identify the inner sum with the definition of `fenchelCoordinateAdjointApply` and
          -- commute the final scalar multiplication.
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [fenchelCoordinateAdjointApply, mul_comm, mul_left_comm, mul_assoc]

/-- The bilinear pairing on perturbation variables `(u, x)` and dual variables `(x⋆, u⋆)`
used to define the adjoint function of the perturbation family. -/
noncomputable def fenchelPerturbationPairing {n m : ℕ}
    (ux : (Fin m → ℝ) × (Fin n → ℝ)) (xStarUStar : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  (∑ i, xStarUStar.1 i * ux.2 i) + ∑ j, xStarUStar.2 j * ux.1 j

/-- Helper for Lemma 31.0.8: after the change of variables `u = v - A x`, the perturbation
pairing `fenchelPerturbationPairing (u, x) (x⋆, u⋆)` splits into an `x`-part and a `v`-part:
the `x`-part uses the shifted dual variable `x⋆ - A⋆ u⋆`, while the `v`-part keeps `u⋆`. -/
lemma helperForLemma_31_0_8_pairing_sub_eq_sum_shifted {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (x : Fin n → ℝ) (v : Fin m → ℝ) :
    fenchelPerturbationPairing (v - A x, x) (xStar, uStar) =
      (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * x i) +
        ∑ j, uStar j * v j := by
  classical
  -- Expand the `u`-part of the pairing and distribute across `v - A x`.
  have hUv :
      (∑ j, uStar j * (v - A x) j) = (∑ j, uStar j * v j) - ∑ j, uStar j * (A x) j := by
    -- Pointwise subtraction gives `uStar j * (v j - (A x) j)`, then finite sums collect.
    simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  -- Rewrite the `A x` pairing against `uStar` using the coordinate adjoint `A⋆ uStar`.
  have hUAx :
      (∑ j, uStar j * (A x) j) = ∑ i, (fenchelCoordinateAdjointApply A uStar) i * x i :=
    helperForLemma_31_0_8_sum_uStar_mul_Ax_eq_sum_adjoint_mul_x (A := A) uStar x
  -- Combine the expansions and regroup the `x`-terms into a single finite sum.
  calc
    fenchelPerturbationPairing (v - A x, x) (xStar, uStar)
        = (∑ i, xStar i * x i) + ∑ j, uStar j * (v - A x) j := by
            simp [fenchelPerturbationPairing]
    _ = (∑ i, xStar i * x i) + ((∑ j, uStar j * v j) - ∑ j, uStar j * (A x) j) := by
          -- Substitute the distributed form of the `u`-part.
          rw [hUv]
    _ = ((∑ i, xStar i * x i) - ∑ j, uStar j * (A x) j) + ∑ j, uStar j * v j := by
          -- Regroup as `(x⋆·x - u⋆·A x) + (u⋆·v)`.
          ring
    _ = ((∑ i, xStar i * x i) - ∑ i, (fenchelCoordinateAdjointApply A uStar) i * x i) +
          ∑ j, uStar j * v j := by
          -- Replace the `A x` term using `hUAx`.
          simp [hUAx]
    _ = (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * x i) + ∑ j, uStar j * v j := by
          -- Turn the difference of finite sums into the finite sum of differences.
          -- This matches the shifted dual variable `xStar - A⋆ uStar`.
          symm
          simpa [sub_mul, Finset.sum_sub_distrib]

/-- The book's adjoint function `F⋆` for the perturbation family
`F(u, x) = f x - g (A x + u)`, obtained as the Fenchel conjugate of the bivariate perturbation
function with respect to the pairing `(u, x)` against `(x⋆, u⋆)`, and viewed as a map sending
`x⋆` to a function of `u⋆`. -/
noncomputable def fenchelPerturbationAdjointFunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    sSup
      (Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
        (fenchelPerturbationPairing ux (xStar, uStar) : EReal) -
          fenchelPerturbationFunction A f g ux)

/-- Helper for Lemma 31.0.8: rewrite `fenchelPerturbationAdjointFunction` after the change of
variables `v = A x + u` (equivalently, `u = v - A x`). This exposes the shifted dual variable
`xStar - A⋆ uStar` in the pairing and replaces `g (A x + u)` by `g v`. -/
lemma helperForLemma_31_0_8_fenchelPerturbationAdjointFunction_changeOfVariables {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    fenchelPerturbationAdjointFunction A f g xStar uStar =
      sSup
        (Set.range fun vx : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((
              (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                ∑ j, uStar j * vx.1 j :
              ℝ) :
              EReal) -
            (f vx.2 - g vx.1)) := by
  classical
  -- Unfold the adjoint function to an `sSup` over the range of an explicit map.
  unfold fenchelPerturbationAdjointFunction
  -- Name the map under the supremum so we can reason about its range.
  let h : ((Fin m → ℝ) × (Fin n → ℝ)) → EReal := fun ux =>
    (fenchelPerturbationPairing ux (xStar, uStar) : EReal) - fenchelPerturbationFunction A f g ux
  change sSup (Set.range h) = _
  -- Change variables `v = A x + u` by showing the two ranges coincide.
  have hRange :
      Set.range h =
        Set.range (fun vx : (Fin m → ℝ) × (Fin n → ℝ) => h (vx.1 - A vx.2, vx.2)) := by
    ext y
    constructor
    · rintro ⟨ux, rfl⟩
      rcases ux with ⟨u, x⟩
      -- The inverse transformation is `(u, x) ↦ (u + A x, x)`.
      refine ⟨(u + A x, x), ?_⟩
      -- After substituting, the `u`-component becomes `(u + A x) - A x = u`.
      simp [h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · rintro ⟨vx, rfl⟩
      -- The forward transformation is `(v, x) ↦ (v - A x, x)`.
      exact ⟨(vx.1 - A vx.2, vx.2), rfl⟩
  -- Rewrite the supremum over the transformed range.
  rw [hRange]
  -- Compute the transformed integrand using the pairing-splitting lemma.
  have hFun :
      (fun vx : (Fin m → ℝ) × (Fin n → ℝ) => h (vx.1 - A vx.2, vx.2)) =
        fun vx : (Fin m → ℝ) × (Fin n → ℝ) =>
          (((
                  (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                    ∑ j, uStar j * vx.1 j :
                  ℝ) :
                  EReal) -
                (f vx.2 - g vx.1)) := by
    funext vx
    -- First simplify the pairing after the substitution `u = v - A x`.
    have hPair :
        fenchelPerturbationPairing (vx.1 - A vx.2, vx.2) (xStar, uStar) =
          (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
            ∑ j, uStar j * vx.1 j := by
      -- This is exactly `helperForLemma_31_0_8_pairing_sub_eq_sum_shifted`.
      simpa using
        helperForLemma_31_0_8_pairing_sub_eq_sum_shifted
          (A := A) (xStar := xStar) (uStar := uStar) (x := vx.2) (v := vx.1)
    have hPairEReal :
        (fenchelPerturbationPairing (vx.1 - A vx.2, vx.2) (xStar, uStar) : EReal) =
          ((
                (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                  ∑ j, uStar j * vx.1 j :
                ℝ) :
            EReal) :=
      congrArg (fun r : ℝ => (r : EReal)) hPair
    -- Next simplify the perturbation term: `A x + (v - A x) = v`.
    have hAx_add_sub : A vx.2 + (vx.1 - A vx.2) = vx.1 := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hPert :
        fenchelPerturbationFunction A f g (vx.1 - A vx.2, vx.2) = f vx.2 - g vx.1 := by
      -- Unfold `fenchelPerturbationFunction` and rewrite `A x + (v - A x)`.
      simp [fenchelPerturbationFunction, hAx_add_sub]
    -- Put the pieces together.
    simp [h, hPairEReal, hPert]
  -- Finish by rewriting the range with the computed integrand.
  rw [hFun]

/-- Helper for Lemma 31.0.8: the supremum of the affine functional `ux ↦ (ux.1 0 : ℝ)` on
`(Fin 1 → ℝ) × (Fin 1 → ℝ)` is `⊤` in `EReal`. This isolates the unbounded-above behavior used in
the counterexample. -/
lemma helperForLemma_31_0_8_sSup_range_fst0_eq_top :
    sSup (Set.range fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) => ((ux.1 0 : ℝ) : EReal)) =
      (⊤ : EReal) := by
  classical
  -- We show there is no real upper bound by producing, for each `μ`, a point with value `μ + 1`.
  refine
    EReal.eq_of_forall_le_coe_iff (a := _) (b := (⊤ : EReal)) (fun μ => ?_)
  constructor
  · intro hle
    -- Choose `ux` with first coordinate equal to the constant function `μ + 1`.
    let u : Fin 1 → ℝ := fun _ => μ + 1
    let x : Fin 1 → ℝ := 0
    let ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) := (u, x)
    have hmem :
        ((μ + 1 : ℝ) : EReal) ∈
          Set.range (fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) => ((ux.1 0 : ℝ) : EReal)) := by
      refine ⟨ux, ?_⟩
      -- Reduce to evaluation at `0 : Fin 1`.
      simp [ux, u]
    have hle_sSup :
        ((μ + 1 : ℝ) : EReal) ≤
          sSup (Set.range fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) => ((ux.1 0 : ℝ) : EReal)) :=
      le_sSup hmem
    have hle' : ((μ + 1 : ℝ) : EReal) ≤ (μ : EReal) := le_trans hle_sSup hle
    have hreal : μ + 1 ≤ μ := (EReal.coe_le_coe_iff).1 hle'
    linarith
  · intro hle
    -- `⊤ ≤ μ` is impossible for any real `μ`.
    exact False.elim (not_top_le_coe μ hle)

/-- Helper for Lemma 31.0.8: the coordinate adjoint action of the zero linear map is the zero
vector. This is used to simplify the closed-form right-hand side in the counterexample. -/
lemma helperForLemma_31_0_8_fenchelCoordinateAdjointApply_zero {n m : ℕ}
    (uStar : Fin m → ℝ) :
    fenchelCoordinateAdjointApply (n := n) (m := m)
        (0 : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) uStar =
      (0 : Fin n → ℝ) := by
  classical
  -- Each coordinate is a sum of coefficients of `A`, and all coefficients vanish when `A = 0`.
  funext i
  simp [fenchelCoordinateAdjointApply]

/-- Helper for Lemma 31.0.8: in the counterexample (`n = m = 1`, `A = 0`, `f = 0`, `g = 0`,
`xStar = 0`, `uStar = 1`), the left-hand side `fenchelPerturbationAdjointFunction` evaluates to
`⊤`. This makes the failure of the claimed closed form completely explicit. -/
lemma helperForLemma_31_0_8_counterexample_lhs_eq_top :
    fenchelPerturbationAdjointFunction
          (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
          (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
          (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) =
        (⊤ : EReal) := by
  classical
  -- Unfold the `sSup` definition and simplify the perturbation term away: when `A = 0`, `f = 0`,
  -- and `g = 0`, the range inside the supremum is exactly the affine functional `ux ↦ ux.1 0`,
  -- whose `sSup` is `⊤` by `helperForLemma_31_0_8_sSup_range_fst0_eq_top`.
  simpa [fenchelPerturbationAdjointFunction, fenchelPerturbationFunction, fenchelPerturbationPairing,
    Fin.sum_univ_one] using helperForLemma_31_0_8_sSup_range_fst0_eq_top

/-- Helper for Lemma 31.0.8: a concrete counterexample (with `n = m = 1`, `A = 0`, `f = 0`,
`g = 0`) showing the claimed closed-form expression for `fenchelPerturbationAdjointFunction`
cannot hold under the current `sSup`-based definition. -/
lemma helperForLemma_31_0_8_counterexample :
    let n : ℕ := 1
    let m : ℕ := 1
    let A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := 0
    let f : (Fin n → ℝ) → EReal := fun _ => (0 : EReal)
    let g : (Fin m → ℝ) → EReal := fun _ => (0 : EReal)
    let xStar : Fin n → ℝ := 0
    let uStar : Fin m → ℝ := fun _ => (1 : ℝ)
    fenchelPerturbationAdjointFunction A f g xStar uStar ≠
      concaveFenchelConjugate g uStar -
        fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar) := by
  classical
  -- Unfold the `let`-binders so we can compute the two sides directly.
  dsimp
  -- First compute the right-hand side: it collapses to `⊥` because `concaveFenchelConjugate 0` is
  -- `⊥` at a nonzero dual vector and `fenchelConjugate 0` at `0` is `0`.
  have huStar_ne : (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    intro h
    have := congrArg (fun u : Fin 1 → ℝ => u 0) h
    simpa using this
  have hAdj : fenchelCoordinateAdjointApply (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
      (fun _ : Fin 1 => (1 : ℝ)) = (0 : Fin 1 → ℝ) := by
    -- The coordinate adjoint is a sum of coefficients of `A`, and all coefficients are `0` when
    -- `A = 0`.
    funext i
    simp [fenchelCoordinateAdjointApply]
  have hFenchel0 :
      fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (0 : Fin 1 → ℝ) = (0 : EReal) := by
    have hfun :
        fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal)) =
          indicatorFunction ({0} : Set (Fin 1 → ℝ)) :=
      section16_fenchelConjugate_const_zero (n := 1)
    have := congrArg (fun h => h (0 : Fin 1 → ℝ)) hfun
    simpa [indicatorFunction] using this
  have hConcave0 :
      concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) =
        (⊥ : EReal) := by
    -- Unfold `concaveFenchelConjugate` and rewrite the convex conjugate using the constant-zero
    -- computation. Since `-(uStar)` is not in `{0}`, the indicator value is `⊤` and negating gives
    -- `⊥`.
    have hfun :
        fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal)) =
          indicatorFunction ({0} : Set (Fin 1 → ℝ)) :=
      section16_fenchelConjugate_const_zero (n := 1)
    have hnot_mem :
        (-fun _ : Fin 1 => (1 : ℝ)) ∉ ({0} : Set (Fin 1 → ℝ)) := by
      -- Membership in `{0}` is equality with the zero function.
      intro hmem
      have heq : (-fun _ : Fin 1 => (1 : ℝ)) = (0 : Fin 1 → ℝ) := by
        simpa using hmem
      -- Evaluate at `0` to get `-1 = 0`.
      have := congrArg (fun u : Fin 1 → ℝ => u 0) heq
      simpa using this
    -- Compute the value at `uStar = 1`.
    simp [concaveFenchelConjugate, hfun, indicatorFunction, hnot_mem]
  have hRhs :
      concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
          fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (fenchelCoordinateAdjointApply (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                (fun _ : Fin 1 => (1 : ℝ)) +
              (0 : Fin 1 → ℝ)) =
        (⊥ : EReal) := by
    -- Reduce to `⊥ - 0 = ⊥`.
    simp [hConcave0, hAdj, hFenchel0]
  -- Next compute the left-hand side: it becomes `⊤` because the supremum includes the unbounded
  -- affine term `u ↦ u 0`.
  have hLhs :
      fenchelPerturbationAdjointFunction (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
          (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (0 : Fin 1 → ℝ)
          (fun _ : Fin 1 => (1 : ℝ)) =
        (⊤ : EReal) := by
    -- Unfold the definition and simplify the perturbation term away.
    have hpair :
        (fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
            (fenchelPerturbationPairing ux ((0 : Fin 1 → ℝ), (fun _ : Fin 1 => (1 : ℝ))) : EReal)) =
          fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) => ((ux.1 0 : ℝ) : EReal) := by
      funext ux
      -- Compute the pairing when `xStar = 0` and `uStar = 1`.
      simp [fenchelPerturbationPairing, Fin.sum_univ_one]
    have hsup :
        sSup
            (Set.range fun ux : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
              (fenchelPerturbationPairing ux ((0 : Fin 1 → ℝ), (fun _ : Fin 1 => (1 : ℝ))) :
                EReal)) =
          (⊤ : EReal) := by
      simpa [hpair] using helperForLemma_31_0_8_sSup_range_fst0_eq_top
    -- With `A = 0`, `f = 0`, and `g = 0`, the perturbation term vanishes and the `sSup` is `⊤`.
    simp [fenchelPerturbationAdjointFunction, fenchelPerturbationFunction, hsup]
  -- Combine the computed values.
  intro hEq
  have hEqTop :
      (⊤ : EReal) =
        concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
          fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (fenchelCoordinateAdjointApply (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                (fun _ : Fin 1 => (1 : ℝ)) +
              (0 : Fin 1 → ℝ)) := by
    simpa [hLhs] using hEq
  have hEqTopBot : (⊤ : EReal) = (⊥ : EReal) := by
    calc
      (⊤ : EReal) =
          concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
            fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
              (fenchelCoordinateAdjointApply (n := 1) (m := 1)
                    (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) (fun _ : Fin 1 => (1 : ℝ)) +
                  (0 : Fin 1 → ℝ)) := hEqTop
      _ = (⊥ : EReal) := hRhs
  exact top_ne_bot hEqTopBot

/-- Helper for Lemma 31.0.8: the closed-form expression claimed for
`fenchelPerturbationAdjointFunction` is not even true in the simplest case
`n = m = 1`, `A = 0`, `f = 0`, `g = 0`; hence a universally quantified proof cannot exist without
an upstream reconciliation of definitions/sign conventions. -/
lemma helperForLemma_31_0_8_universalExpression_false :
    let n : ℕ := 1
    let m : ℕ := 1
    let A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := 0
    let f : (Fin n → ℝ) → EReal := fun _ => (0 : EReal)
    let g : (Fin m → ℝ) → EReal := fun _ => (0 : EReal)
    ¬ (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar =
          concaveFenchelConjugate g uStar -
            fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar)) := by
  classical
  -- Unfold the `let`-binders so we can specialize the claimed formula at the values used in the
  -- explicit counterexample.
  dsimp
  intro hall
  -- Specialize the supposed identity at `xStar = 0` and `uStar = 1`.
  have hEq := hall (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ))
  -- The counterexample lemma shows this specialized equality is impossible.
  have hNe :
      fenchelPerturbationAdjointFunction
            (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
            (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) ≠
          concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
            fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
              (fenchelCoordinateAdjointApply
                    (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                    (fun _ : Fin 1 => (1 : ℝ)) +
                (0 : Fin 1 → ℝ)) := by
    simpa using helperForLemma_31_0_8_counterexample
  exact hNe hEq

/-- Helper for Lemma 31.0.8: the hypotheses of the textbook lemma are satisfiable (e.g. by
constant functions), and the claimed closed form nevertheless fails under the current `sSup`-based
definition of `fenchelPerturbationAdjointFunction`. -/
lemma helperForLemma_31_0_8_hypothesesSatisfiable_and_formulaFails :
    ∃ (n m : ℕ)
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
      (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal),
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
      ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g ∧
      ∃ xStar : Fin n → ℝ, ∃ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar ≠
          concaveFenchelConjugate g uStar -
            fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar) := by
  classical
  -- We reuse the explicit `n = m = 1` counterexample with `A = 0`, `f = 0`, and `g = 0`.
  have hf0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : (Fin 1 → ℝ) => (0 : EReal)) := by
    -- A finite constant function is proper convex on `Set.univ`.
    simpa using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  have hg0 :
      ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : (Fin 1 → ℝ) => (0 : EReal)) := by
    -- Proper concavity is encoded as proper convexity of the negation.
    simpa [ProperConcaveFunctionOn] using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  have hFails :
      fenchelPerturbationAdjointFunction
            (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
            (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) ≠
          concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
            fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
              (fenchelCoordinateAdjointApply
                    (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                    (fun _ : Fin 1 => (1 : ℝ)) +
                (0 : Fin 1 → ℝ)) := by
    -- The specialized inequality is exactly the `let`-based counterexample lemma.
    simpa using helperForLemma_31_0_8_counterexample
  refine ⟨1, 1, (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)), (fun _ => (0 : EReal)),
    (fun _ => (0 : EReal)), hf0, hg0, ?_⟩
  -- Provide the explicit dual variables from the counterexample.
  exact ⟨(0 : Fin 1 → ℝ), (fun _ : Fin 1 => (1 : ℝ)), hFails⟩

/-- Helper for Lemma 31.0.8: there exist proper convex/concave data for which the universally
quantified closed-form identity in `fenchelPerturbationAdjointFunction_expression` fails. -/
lemma helperForLemma_31_0_8_hypothesesSatisfiable_and_universalFormulaFails :
    ∃ (n m : ℕ)
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
      (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal),
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
      ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g ∧
      ¬ (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
          fenchelPerturbationAdjointFunction A f g xStar uStar =
            concaveFenchelConjugate g uStar -
              fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar)) := by
  classical
  -- Extract the explicit counterexample data where the closed-form identity fails at some dual
  -- variables `xStar` and `uStar`.
  rcases helperForLemma_31_0_8_hypothesesSatisfiable_and_formulaFails with
    ⟨n, m, A, f, g, hf, hg, xStar, uStar, hne⟩
  refine ⟨n, m, A, f, g, hf, hg, ?_⟩
  intro hall
  -- Specialize the universal claim at the witness values to contradict `hne`.
  exact hne (hall xStar uStar)

/-- Helper for Lemma 31.0.8: express the convex Fenchel conjugate of `-g` in terms of the book's
concave conjugate `concaveFenchelConjugate g` by a sign flip on the dual variable. This isolates
the convention mismatch responsible for the counterexample. -/
lemma helperForLemma_31_0_8_fenchelConjugate_neg_eq_neg_concaveFenchelConjugate_neg {m : ℕ}
    (g : (Fin m → ℝ) → EReal) (uStar : Fin m → ℝ) :
    fenchelConjugate m (fun u => -(g u)) uStar = - concaveFenchelConjugate g (-uStar) := by
  -- Unfold the definition of the concave conjugate and simplify the double negations.
  simp [concaveFenchelConjugate]

/-- Helper for Lemma 31.0.8: split the transformed integrand (after the change of variables
`v = A x + u`) into an `x`-only term and a `v`-only term. This is the algebraic step that
prepares the supremum decomposition. -/
lemma helperForLemma_31_0_8_transformedIntegrand_eq_sumSeparated {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (vx : (Fin m → ℝ) × (Fin n → ℝ)) :
    ((
          (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
            ∑ j, uStar j * vx.1 j :
          ℝ) :
        EReal) -
        (f vx.2 - g vx.1) =
      ((((∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i : ℝ) : EReal) - f vx.2) +
        (((∑ j, uStar j * vx.1 j : ℝ) : EReal) - (fun u => -(g u)) vx.1)) := by
  classical
  -- We will use `EReal.neg_sub` to rewrite `-(f x - g v)` as `-f x + g v`.
  have hx_univ : vx.2 ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hf_ne_bot : f vx.2 ≠ (⊥ : EReal) := hf.2.2 vx.2 hx_univ
  have hneg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hv_univ : vx.1 ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hneg_ne_bot : -(g vx.1) ≠ (⊥ : EReal) := hneg_proper.2.2 vx.1 hv_univ
  have hg_ne_top : g vx.1 ≠ (⊤ : EReal) := by
    intro htop
    have : -(g vx.1) = (⊥ : EReal) := by
      simpa [htop]
    exact hneg_ne_bot this
  -- Now expand the subtraction and regroup into `x`-only and `v`-only parts.
  calc
    ((
          (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
            ∑ j, uStar j * vx.1 j :
          ℝ) :
        EReal) -
        (f vx.2 - g vx.1)
        =
        ((
              (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                ∑ j, uStar j * vx.1 j :
              ℝ) :
            EReal) +
          (-(f vx.2 - g vx.1)) := by
          simp [sub_eq_add_neg]
    _ =
        ((
              (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                ∑ j, uStar j * vx.1 j :
              ℝ) :
            EReal) +
          (-f vx.2 + g vx.1) := by
          -- `hf_ne_bot` supplies `f x ≠ ⊥`, and `hg_ne_top` supplies `g v ≠ ⊤`.
          rw [EReal.neg_sub (Or.inl hf_ne_bot) (Or.inr hg_ne_top)]
    _ =
        ((((∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i : ℝ) : EReal) - f vx.2) +
          (((∑ j, uStar j * vx.1 j : ℝ) : EReal) - (fun u => -(g u)) vx.1)) := by
          -- Coercions commute with addition, and the remaining rearrangement is by associativity
          -- and commutativity of `EReal` addition plus `sub_eq_add_neg`.
          simp [sub_eq_add_neg, EReal.coe_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 31.0.8: rewrite the range of a separated sum over pairs as a `Set.image2`
range of sums. This is the bridge that lets us use
`section16_sSup_image2_add_eq_sSup_add`. -/
lemma helperForLemma_31_0_8_transformedRange_eq_image2SeparatedRanges {n m : ℕ}
    (xPart : (Fin n → ℝ) → EReal) (vPart : (Fin m → ℝ) → EReal) :
    Set.range (fun vx : (Fin m → ℝ) × (Fin n → ℝ) => xPart vx.2 + vPart vx.1) =
      Set.image2 (· + ·) (Set.range xPart) (Set.range vPart) := by
  -- Membership in the range of the pair map is exactly membership in the image2 of the two
  -- coordinate ranges.
  ext z
  constructor
  · rintro ⟨vx, rfl⟩
    refine ⟨xPart vx.2, ?_, vPart vx.1, ?_, rfl⟩
    · exact ⟨vx.2, rfl⟩
    · exact ⟨vx.1, rfl⟩
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨v, rfl⟩, rfl⟩
    exact ⟨(v, x), rfl⟩

/-- Helper for Lemma 31.0.8: identify the `x`-part supremum with a Fenchel conjugate at the
shifted dual vector `xStar - A⋆ uStar`. -/
lemma helperForLemma_31_0_8_sSup_xPart_eq_fenchelConjugate_shifted {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    sSup
        (Set.range fun x : Fin n → ℝ =>
          (((∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * x i : ℝ) : EReal) - f x)) =
      fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) := by
  -- Unfold `fenchelConjugate` and simplify the finite-sum expression to the dot product.
  simp [fenchelConjugate, sSup_range, dotProduct, Pi.sub_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 31.0.8: identify the `v`-part supremum with the Fenchel conjugate of `-g`. -/
lemma helperForLemma_31_0_8_sSup_vPart_eq_fenchelConjugate_neg {m : ℕ}
    (g : (Fin m → ℝ) → EReal) (uStar : Fin m → ℝ) :
    sSup
        (Set.range fun v : Fin m → ℝ =>
          (((∑ j, uStar j * v j : ℝ) : EReal) - (fun u => -(g u)) v)) =
      fenchelConjugate m (fun u => -(g u)) uStar := by
  -- This is exactly `fenchelConjugate` with the commuted dot product.
  simp [fenchelConjugate, sSup_range, dotProduct, mul_comm, mul_left_comm, mul_assoc]

-- Proof sketch: identify the perturbation adjoint `F⋆` by taking the Fenchel conjugate in the
-- perturbation variables, separate the `g` and `f` contributions, and rewrite the linear term
-- `⟪A x, u⋆⟫` as `⟪x, A⋆ u⋆⟫` using the coordinate adjoint action of `A`.
/-- Lemma 31.0.8 (Expression of the Adjoint Function of `F`): let
`f : ℝ^n → ℝ ∪ {+∞}` be proper convex, let `g : ℝ^m → ℝ ∪ {-∞}` be proper concave, and let
`A : ℝ^n → ℝ^m` be linear. For the perturbation family `F(u, x) = f x - g (A x + u)`, the
adjoint function `F⋆` is given by
`(F⋆ xStar) uStar = f⋆(xStar - A⋆ uStar) - g⋆(-uStar)`, where `g⋆` is the book's concave
Fenchel conjugate of `g`, `f⋆` is the Fenchel conjugate of `f`, and `A⋆ uStar` is
`fenchelCoordinateAdjointApply A uStar`. -/
lemma fenchelPerturbationAdjointFunction_expression {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
      fenchelPerturbationAdjointFunction A f g xStar uStar =
        fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
          concaveFenchelConjugate g (-uStar) := by
  -- Proof sketch: unfold the adjoint definition, make the change of variables `v = A x + u`,
  -- separate the resulting supremum into the `x`-part and the `v`-part, and identify those two
  -- suprema with `f⋆ (x⋆ - A⋆ u⋆)` and `-g⋆(-u⋆)`, respectively.
  intro xStar uStar
  -- First rewrite the adjoint supremum after the substitution `v = A x + u`.
  rw [helperForLemma_31_0_8_fenchelPerturbationAdjointFunction_changeOfVariables
    (A := A) (f := f) (g := g) (xStar := xStar) (uStar := uStar)]
  let xPart : (Fin n → ℝ) → EReal := fun x =>
    (((∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * x i : ℝ) : EReal) - f x)
  let vPart : (Fin m → ℝ) → EReal := fun v =>
    (((∑ j, uStar j * v j : ℝ) : EReal) - (fun u => -(g u)) v)
  -- Next separate the transformed integrand into its `x` and `v` contributions.
  have hSeparated :
      (fun vx : (Fin m → ℝ) × (Fin n → ℝ) =>
        ((
              (∑ i, (xStar i - (fenchelCoordinateAdjointApply A uStar) i) * vx.2 i) +
                ∑ j, uStar j * vx.1 j :
              ℝ) :
            EReal) -
          (f vx.2 - g vx.1)) =
        fun vx : (Fin m → ℝ) × (Fin n → ℝ) => xPart vx.2 + vPart vx.1 := by
    funext vx
    -- This is exactly the algebraic splitting lemma for the transformed integrand.
    simpa [xPart, vPart] using
      helperForLemma_31_0_8_transformedIntegrand_eq_sumSeparated
        (A := A) (f := f) (g := g) (xStar := xStar) (uStar := uStar)
        (hf := hf) (hg := hg) (vx := vx)
  rw [hSeparated]
  -- Rewrite the bivariate range as the `image2` of the separate `x`- and `v`-ranges.
  rw [helperForLemma_31_0_8_transformedRange_eq_image2SeparatedRanges
    (xPart := xPart) (vPart := vPart)]
  -- The supremum of pairwise sums splits as the sum of the two suprema.
  rw [section16_sSup_image2_add_eq_sSup_add]
  -- Identify the `x`-supremum with the shifted Fenchel conjugate of `f`.
  have hx :
      sSup (Set.range xPart) =
        fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) := by
    simpa [xPart] using
      helperForLemma_31_0_8_sSup_xPart_eq_fenchelConjugate_shifted
        (A := A) (f := f) (xStar := xStar) (uStar := uStar)
  -- Identify the `v`-supremum with the Fenchel conjugate of `-g`.
  have hv :
      sSup (Set.range vPart) =
        fenchelConjugate m (fun u => -(g u)) uStar := by
    simpa [vPart] using
      helperForLemma_31_0_8_sSup_vPart_eq_fenchelConjugate_neg
        (g := g) (uStar := uStar)
  rw [hx, hv]
  -- Convert the convex conjugate of `-g` back to the book's concave conjugate convention.
  rw [helperForLemma_31_0_8_fenchelConjugate_neg_eq_neg_concaveFenchelConjugate_neg
    (g := g) (uStar := uStar)]
  simp [sub_eq_add_neg]

/-- The dual concave objective `u⋆ ↦ g⋆ u⋆ - f⋆ (A⋆ u⋆)` associated with the perturbation
family `F(u, x) = f x - g (A x + u)`. -/
noncomputable def fenchelDualConcaveObjective {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin m → ℝ) → EReal :=
  fun uStar =>
    fenchelConjugate n f (-fenchelCoordinateAdjointApply A uStar) -
      concaveFenchelConjugate g (-uStar)

/-- The dual perturbation value function `x⋆ ↦ sup_{u⋆} (F⋆ x⋆) u⋆` for the adjoint family
`F⋆`. Evaluating at `x⋆ = 0` gives the textbook quantity `sup F⋆ 0`. -/
noncomputable def fenchelDualPerturbationValueFunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar =>
    ⨆ uStar : Fin m → ℝ,
      fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
        concaveFenchelConjugate g (-uStar)

/-- The dual concave program `(P*)` is strongly consistent when the origin lies in the relative
interior of the effective domain of its dual value function, viewed as a concave function of the
perturbation variable `x⋆`. -/
def FenchelDualProgramStronglyConsistent {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) : Prop :=
  ∃ uStar : Fin m → ℝ,
    uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
      fenchelCoordinateAdjointApply A uStar ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))

end Section31
end Chap06
