/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part14

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.7: bridge the real partial subdifferentials on `C` and `D` to the
Chapter 23 `EReal` subdifferential of the one-variable convex extensions used in the proof. -/
lemma helperForTheorem_35_7_realPartialSubdifferential_bridges
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ} (hu : u ∈ C) (hv : v ∈ D) :
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    (∀ uStar : Fin m → ℝ,
        uStar ∈ realPartialSubdifferentialInFirstVariableOn C K u v ↔
          dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt f u) ∧
      (∀ vStar : Fin n → ℝ,
        vStar ∈ realPartialSubdifferentialInSecondVariableOn D K u v ↔
          dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt g v) := by
  classical
  intro f g
  constructor
  · intro uStar
    -- Unfold the two definitions and rewrite the `EReal` inequality into a real inequality.
    constructor
    · intro huStar
      -- Show `dotProductEquiv (-uStar)` is a subgradient of `f` at `u`.
      -- The `⊤` branch is trivial; on `C` we reduce to the defining inequality of `uStar`.
      intro z
      by_cases hz : z ∈ C
      · have huC : u ∈ C := hu
        have hineq : K z v ≤ K u v + ∑ i : Fin m, uStar i * (z i - u i) := huStar z hz
        have hpair :
            ((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) =
              -((∑ i : Fin m, uStar i * (z i - u i)) : ℝ) := by
          -- `dotProductEquiv` is the dot product; the `-uStar` flips the sign.
          simp [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc, mul_assoc, mul_left_comm, mul_comm]
        -- Translate to `EReal` using coercions and arithmetic.
        have : ((-(K z v) : ℝ) : EReal) ≥
            ((-(K u v) : ℝ) : EReal) + (((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) : ℝ) := by
          -- Move everything to the real side, then coerce.
          have : (-(K z v) : ℝ) ≥ (-(K u v) : ℝ) + ((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) := by
            -- Rewrite the pairing term using `hpair`, then finish by linear arithmetic on `hineq`.
            rw [hpair]
            linarith [hineq]
          exact (EReal.coe_le_coe_iff).2 this
        -- Finish by unfolding `f` and `IsSubgradientAt`.
        simpa [IsSubgradientAt, subdifferentialAt, f, hz, huC] using this
      · -- Outside `C`, `f z = ⊤`, so the inequality is automatic.
        have : (⊤ : EReal) ≥ f u + (((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) : ℝ) := by
          simpa using (le_top : f u + (((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) : ℝ) ≤ (⊤ : EReal))
        simpa [IsSubgradientAt, subdifferentialAt, f, hz] using this
    · intro huStarSub
      -- Assume `dotProductEquiv (-uStar)` is a subgradient of `f` at `u`; recover the real
      -- partial-subdifferential inequalities on `C`.
      intro z hz
      have huC : u ∈ C := hu
      have hzIneq :
          f z ≥ f u + (((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) : ℝ) := huStarSub z
      -- Rewrite this inequality on `C` into the real inequality.
      have hzIneq' :
          (-(K z v) : ℝ) ≥ (-(K u v) : ℝ) + ((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) := by
        -- Unfold `f` on `C` and use `EReal.coe_le_coe_iff`.
        have : ((-(K z v) : ℝ) : EReal) ≥ ((-(K u v) : ℝ) : EReal) +
            (((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) : ℝ) := by
          simpa [f, hz, huC] using hzIneq
        exact (EReal.coe_le_coe_iff).1 this
      -- Evaluate the dot product equivalence and rearrange.
      have hpair :
          ((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) =
            -((∑ i : Fin m, uStar i * (z i - u i)) : ℝ) := by
        simp [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc, mul_assoc, mul_left_comm, mul_comm]
      -- Convert `-(K z v) ≥ -(K u v) + ...` into `K z v ≤ K u v + Σ ...`.
      have : K z v ≤ K u v + ∑ i : Fin m, uStar i * (z i - u i) := by
        have hzIneq2 :
            (-(K z v) : ℝ) ≥ (-(K u v) : ℝ) + ((dotProductEquiv ℝ (Fin m)) (-uStar)) (z - u) := hzIneq'
        have hzIneq3 :
            (-(K z v) : ℝ) ≥ (-(K u v) : ℝ) + -((∑ i : Fin m, uStar i * (z i - u i)) : ℝ) := by
          -- Rewrite the pairing term using `hpair`.
          have hzIneq3 := hzIneq2
          rw [hpair] at hzIneq3
          exact hzIneq3
        linarith [hzIneq3]
      exact this
  · intro vStar
    constructor
    · intro hvStar
      intro z
      by_cases hz : z ∈ D
      · have hvD : v ∈ D := hv
        have hineq : K u z ≥ K u v + ∑ i : Fin n, vStar i * (z i - v i) := hvStar z hz
        have hpair :
            ((dotProductEquiv ℝ (Fin n)) vStar) (z - v) =
              (∑ i : Fin n, vStar i * (z i - v i)) := by
          simp [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg]
        have : ((K u z : ℝ) : EReal) ≥ ((K u v : ℝ) : EReal) +
            (((dotProductEquiv ℝ (Fin n)) vStar) (z - v) : ℝ) := by
          have : (K u z : ℝ) ≥ (K u v : ℝ) + ((dotProductEquiv ℝ (Fin n)) vStar) (z - v) := by
            simpa [hpair] using hineq
          exact (EReal.coe_le_coe_iff).2 this
        simpa [IsSubgradientAt, subdifferentialAt, g, hz, hvD] using this
      · have : (⊤ : EReal) ≥ g v + (((dotProductEquiv ℝ (Fin n)) vStar) (z - v) : ℝ) := by
          simpa using (le_top : g v + (((dotProductEquiv ℝ (Fin n)) vStar) (z - v) : ℝ) ≤ (⊤ : EReal))
        simpa [IsSubgradientAt, subdifferentialAt, g, hz] using this
    · intro hvStarSub
      intro z hz
      have hvD : v ∈ D := hv
      have hzIneq :
          g z ≥ g v + (((dotProductEquiv ℝ (Fin n)) vStar) (z - v) : ℝ) := hvStarSub z
      have hzIneq' :
          (K u z : ℝ) ≥ (K u v : ℝ) + ((dotProductEquiv ℝ (Fin n)) vStar) (z - v) := by
        have : ((K u z : ℝ) : EReal) ≥ ((K u v : ℝ) : EReal) +
            (((dotProductEquiv ℝ (Fin n)) vStar) (z - v) : ℝ) := by
          simpa [g, hz, hvD] using hzIneq
        exact (EReal.coe_le_coe_iff).1 this
      have hpair :
          ((dotProductEquiv ℝ (Fin n)) vStar) (z - v) =
            (∑ i : Fin n, vStar i * (z i - v i)) := by
        simp [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg]
      have : K u z ≥ K u v + ∑ i : Fin n, vStar i * (z i - v i) := by
        simpa [hpair] using hzIneq'
      exact this

/-- Helper for Theorem 35.7: combine max-norm bounds on coordinate errors into membership in the
split Euclidean closed ball `splitEuclideanClosedBall ε` (defined by coordinate squares). -/
lemma helperForTheorem_35_7_splitBall_combine_errors
    {m n : ℕ} {ε δ : ℝ}
    (hδnonneg : 0 ≤ δ)
    (hδ : ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ))
    {du : Fin m → ℝ} {dv : Fin n → ℝ}
    (hdu : ‖du‖ ≤ δ) (hdv : ‖dv‖ ≤ δ) :
    ((du, dv) : (Fin m → ℝ) × (Fin n → ℝ)) ∈ splitEuclideanClosedBall (m := m) (n := n) ε := by
  classical
  -- Unfold the split-ball definition; it is a coordinate-square inequality.
  simp [splitEuclideanClosedBall] at ⊢
  -- Step 1: bound each coordinate square by `δ^2` using the `Pi`-norm bound `‖du i‖ ≤ ‖du‖`.
  have hdu_coord : ∀ i : Fin m, du i ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
    intro i
    have hi : ‖du i‖ ≤ ‖du‖ := norm_le_pi_norm du i
    have hi' : |du i| ≤ δ := by
      have : |du i| ≤ ‖du‖ := by simpa [Real.norm_eq_abs] using hi
      exact le_trans this hdu
    have hsq : |du i| ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
      -- Squaring is monotone on nonnegative reals.
      simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg (du i)) hi')
    simpa [sq_abs] using hsq
  have hdv_coord : ∀ j : Fin n, dv j ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
    intro j
    have hj : ‖dv j‖ ≤ ‖dv‖ := norm_le_pi_norm dv j
    have hj' : |dv j| ≤ δ := by
      have : |dv j| ≤ ‖dv‖ := by simpa [Real.norm_eq_abs] using hj
      exact le_trans this hdv
    have hsq : |dv j| ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by
      simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg (dv j)) hj')
    simpa [sq_abs] using hsq
  -- Step 2: sum the coordinatewise bounds.
  have hsum_du : (∑ i : Fin m, du i ^ (2 : ℕ)) ≤ (m : ℝ) * (δ ^ (2 : ℕ)) := by
    have hsum :
        (∑ i : Fin m, du i ^ (2 : ℕ)) ≤ ∑ _i : Fin m, (δ ^ (2 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => hdu_coord i)
    have hconst : (∑ _i : Fin m, (δ ^ (2 : ℕ))) = (m : ℝ) * (δ ^ (2 : ℕ)) := by simp
    simpa [hconst] using hsum
  have hsum_dv : (∑ j : Fin n, dv j ^ (2 : ℕ)) ≤ (n : ℝ) * (δ ^ (2 : ℕ)) := by
    have hsum :
        (∑ j : Fin n, dv j ^ (2 : ℕ)) ≤ ∑ _j : Fin n, (δ ^ (2 : ℕ)) :=
      Finset.sum_le_sum (fun j _ => hdv_coord j)
    have hconst : (∑ _j : Fin n, (δ ^ (2 : ℕ))) = (n : ℝ) * (δ ^ (2 : ℕ)) := by simp
    simpa [hconst] using hsum
  have hsum_total :
      (∑ i : Fin m, du i ^ (2 : ℕ)) + (∑ j : Fin n, dv j ^ (2 : ℕ)) ≤
        ((m + n : ℕ) : ℝ) * (δ ^ (2 : ℕ)) := by
    have hmn :
        (m : ℝ) * (δ ^ (2 : ℕ)) + (n : ℝ) * (δ ^ (2 : ℕ)) =
          ((m + n : ℕ) : ℝ) * (δ ^ (2 : ℕ)) := by
      simp [Nat.cast_add, add_mul]
    have := add_le_add hsum_du hsum_dv
    simpa [hmn] using this
  -- Step 3: combine with the numeric hypothesis.
  exact le_trans hsum_total hδ

-- Proof sketch: apply the Chapter 24 upper-semicontinuity theorem for convex pointwise limits to
-- the convex slices `u ↦ -K(·, v)` and `v ↦ K(u, ·)` on the open convex sets `C` and `D`. The
-- first application gives the lower semicontinuity of the `u`-directional derivative after
-- restoring the sign, the second gives the upper semicontinuity in the `v`-variable, and the
-- eventual subdifferential inclusion follows by combining the two one-variable inclusions in
-- product coordinates with the Euclidean `ε`-ball in `ℝ^(m+n)`.
/-- Theorem 35.7: let `K` be a concave-convex real-valued function on an open convex product
`C × D ⊆ ℝ^m × ℝ^n`, and let `K₁, K₂, ...` be concave-convex real-valued functions on `C × D`
converging pointwise to `K`. If `(uᵢ, vᵢ) ∈ C × D` converges to `(u, v)`, then for every
`u' ∈ ℝ^m` the first-variable directional derivatives satisfy
`liminf Kᵢ'(uᵢ, vᵢ; u', 0) ≥ K'(u, v; u', 0)`, for every `v' ∈ ℝ^n` the second-variable
directional derivatives satisfy `limsup Kᵢ'(uᵢ, vᵢ; 0, v') ≤ K'(u, v; 0, v')`, and for every
`ε > 0` the saddle subdifferentials eventually satisfy
`∂ Kᵢ (uᵢ, vᵢ) ⊆ ∂ K (u, v) + ε B`, where `B` is the Euclidean unit ball in `ℝ^(m+n)`. -/
theorem section35_theorem35_7
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hKSeq : ∀ i : ℕ, IsRealConcaveConvexOn C D (KSeq i))
    (hpoint :
      ∀ u₀ ∈ C, ∀ v₀ ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ v₀) Filter.atTop (nhds (K u₀ v₀)))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (uSeq : ℕ → Fin m → ℝ) (vSeq : ℕ → Fin n → ℝ)
    (huSeq : ∀ i : ℕ, uSeq i ∈ C) (hvSeq : ∀ i : ℕ, vSeq i ∈ D)
    (huSeq_tendsto : Filter.Tendsto uSeq Filter.atTop (nhds u))
    (hvSeq_tendsto : Filter.Tendsto vSeq Filter.atTop (nhds v)) :
    (∀ u' : Fin m → ℝ,
      ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) ≤
        Filter.liminf
          (fun i : ℕ =>
            ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
              EReal))
          Filter.atTop) ∧
    (∀ v' : Fin n → ℝ,
      Filter.limsup
          (fun i : ℕ =>
            ((realSecondVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) v' : ℝ) :
              EReal))
          Filter.atTop ≤
        ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
      realSaddleSubdifferentialOn C D (KSeq i) (uSeq i) (vSeq i) ⊆
        Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
          (realSaddleSubdifferentialOn C D K u v)
          (splitEuclideanClosedBall (m := m) (n := n) ε) := by
  classical
  -- The proof follows the textbook route: apply the Chapter 24 pointwise-limit theorem to the
  -- convex slices `u ↦ -K(u,v)` and `v ↦ K(u,v)`, then translate back to the two-variable saddle
  -- derivatives and saddle subdifferentials.
  rcases
      helperForTheorem_35_7_pointwiseTendsto_movingSlices
        (C := C) (D := D) (K := K) (KSeq := KSeq)
        hC_open hD_open hC_conv hD_conv hKSeq hpoint hu hv
        uSeq vSeq huSeq hvSeq huSeq_tendsto hvSeq_tendsto with
    ⟨hpoint_uSlices, hpoint_vSlices⟩

  -- Step 1: the first-variable `liminf` inequality is obtained by applying Chapter 24 to the
  -- convex `⊤`-extensions of the slices and then undoing the sign.
  have hFirstIneq :
      ∀ u' : Fin m → ℝ,
        ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) ≤
          Filter.liminf
            (fun i : ℕ =>
              ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
                EReal))
            Filter.atTop := by
    intro u'
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let fSeq : ℕ → (Fin m → ℝ) → EReal :=
      fun i x => if x ∈ C then ((-(KSeq i x (vSeq i)) : ℝ) : EReal) else (⊤ : EReal)
    have hf_convOn : ConvexOn ℝ C (fun x => (-(K x v) : ℝ)) := by
      -- `simp` tries to rewrite `ConvexOn (-f)` into a `ConcaveOn f` goal; avoid it.
      exact (hK.1 v hv).neg
    have hf : ConvexFunction f :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (s := C) (f := fun x => (-(K x v) : ℝ))
        hf_convOn).1
    have hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
      intro z hz
      simp [f, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ C (fun x => (-(KSeq i x (vSeq i)) : ℝ)) := by
        -- As above, avoid `simpa` to prevent rewriting `ConvexOn (-f)` into a `ConcaveOn f` goal.
        exact ((hKSeq i).1 (vSeq i) (hvSeq i)).neg
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (s := C) (f := fun x => (-(KSeq i x (vSeq i)) : ℝ)) hconvOn).1
    have hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [fSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_f : ∀ z ∈ C, Filter.Tendsto (fun i : ℕ => fSeq i z) Filter.atTop (nhds (f z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i z (vSeq i)) Filter.atTop (nhds (K z v)) :=
        hpoint_uSlices z hz
      simpa [f, fSeq, hz] using (helperForTheorem_5_24_8_tendsto_coe_of_tendsto (hu := hzT.neg))
    have hChapter24 :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := C) hC_open hC_conv hf hf_finite fSeq hfSeq hfSeq_finite hu uSeq huSeq huSeq_tendsto
        hpoint_f
    have hLimsup :
        Filter.limsup (fun i : ℕ => upperDirectionalDerivativeAt (fSeq i) (uSeq i) u')
            Filter.atTop ≤ upperDirectionalDerivativeAt f u u' := by
      simpa using hChapter24.1 u' (fun _ : ℕ => u')
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => u') Filter.atTop (nhds u'))
    -- Rewrite in terms of the packaged real saddle directional derivatives.
    have hbridgeLimit :
        ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) =
          -upperDirectionalDerivativeAt f u u' := by
      simpa [f] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv u' (0 : Fin n → ℝ)).1
    have hbridgeSeq :
        ∀ i : ℕ,
          ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) : EReal) =
            -upperDirectionalDerivativeAt (fSeq i) (uSeq i) u' := by
      intro i
      simpa [fSeq] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := KSeq i) hC_open hD_open hC_conv hD_conv (hKSeq i)
          (huSeq i) (hvSeq i) u' (0 : Fin n → ℝ)).1
    have hLimsup' :
        Filter.limsup
            (fun i : ℕ =>
              -((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
                EReal))
            Filter.atTop ≤
          -((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) := by
      -- Substitute the bridge equalities into the Chapter 24 inequality.
      simpa [hbridgeLimit, hbridgeSeq] using hLimsup
    -- Convert the `limsup` inequality under negation into the desired `liminf` inequality.
    exact helperForTheorem_35_7_ereal_liminf_of_limsup_neg hLimsup'

  -- Step 2: the second-variable `limsup` inequality follows directly from Chapter 24 on the
  -- convex slices `v ↦ K(u,v)`.
  have hSecondIneq :
      ∀ v' : Fin n → ℝ,
        Filter.limsup
            (fun i : ℕ =>
              ((realSecondVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) v' : ℝ) :
                EReal))
            Filter.atTop ≤
          ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) := by
    intro v'
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    let gSeq : ℕ → (Fin n → ℝ) → EReal :=
      fun i y => if y ∈ D then ((KSeq i (uSeq i) y : ℝ) : EReal) else (⊤ : EReal)
    have hg_convOn : ConvexOn ℝ D (fun y => (K u y : ℝ)) := (hK.2 u hu)
    have hg : ConvexFunction g :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (s := D) (f := fun y => (K u y : ℝ))
        hg_convOn).1
    have hg_finite : ∀ z ∈ D, g z ≠ (⊤ : EReal) ∧ g z ≠ (⊥ : EReal) := by
      intro z hz
      simp [g, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hgSeq : ∀ i, ConvexFunction (gSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ D (fun y => (KSeq i (uSeq i) y : ℝ)) := (hKSeq i).2 (uSeq i) (huSeq i)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (s := D) (f := fun y => (KSeq i (uSeq i) y : ℝ)) hconvOn).1
    have hgSeq_finite : ∀ i, ∀ z ∈ D, gSeq i z ≠ (⊤ : EReal) ∧ gSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [gSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_g : ∀ z ∈ D, Filter.Tendsto (fun i : ℕ => gSeq i z) Filter.atTop (nhds (g z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) z) Filter.atTop (nhds (K u z)) :=
        hpoint_vSlices z hz
      simpa [g, gSeq, hz] using (helperForTheorem_5_24_8_tendsto_coe_of_tendsto hzT)
    have hChapter24 :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := D) hD_open hD_conv hg hg_finite gSeq hgSeq hgSeq_finite hv vSeq hvSeq hvSeq_tendsto
        hpoint_g
    have hLimsup :
        Filter.limsup (fun i : ℕ => upperDirectionalDerivativeAt (gSeq i) (vSeq i) v')
            Filter.atTop ≤ upperDirectionalDerivativeAt g v v' := by
      simpa using hChapter24.1 v' (fun _ : ℕ => v')
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => v') Filter.atTop (nhds v'))
    have hbridgeLimit :
        ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) =
          upperDirectionalDerivativeAt g v v' := by
      simpa [g] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv (0 : Fin m → ℝ) v').2
    have hbridgeSeq :
        ∀ i : ℕ,
          ((realSecondVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) v' : ℝ) : EReal) =
            upperDirectionalDerivativeAt (gSeq i) (vSeq i) v' := by
      intro i
      simpa [gSeq] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := KSeq i) hC_open hD_open hC_conv hD_conv (hKSeq i)
          (huSeq i) (hvSeq i) (0 : Fin m → ℝ) v').2
    simpa [hbridgeLimit, hbridgeSeq] using hLimsup

  -- Step 3: the eventual saddle-subdifferential inclusion comes from combining the two one-variable
  -- Chapter 24 inclusions and packaging the product error in `splitEuclideanClosedBall`.
  have hEventuallySubdiff :
      ∀ ε : ℝ, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        realSaddleSubdifferentialOn C D (KSeq i) (uSeq i) (vSeq i) ⊆
          Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
            (realSaddleSubdifferentialOn C D K u v)
            (splitEuclideanClosedBall (m := m) (n := n) ε) := by
    -- Route: reuse the (already-proved) subdifferential bridges and the split-ball combination lemma.
    intro ε hε
    -- The heavy lifting of the eventual inclusion is already present later in the file as a commented block;
    -- here we invoke that structure via the same Chapter 24 theorem and the partial-subdifferential bridges.
    -- To keep this theorem self-contained, we reuse exactly the same construction as in the sketch.
    -- (The details are long but routine bookkeeping, and are handled below.)
    -- This portion mirrors the commented proof block and uses the already-proved bridge lemmas.
    let A : ℝ := ((m + n + 1 : ℕ) : ℝ)
    let δ : ℝ := ε / Real.sqrt A
    have hApos : 0 < A := by
      dsimp [A]
      exact_mod_cast (Nat.succ_pos (m + n))
    have hδpos : 0 < δ := by
      have hsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
      exact div_pos hε hsqrtpos
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hδineq : ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by
      -- `(m+n) * (ε/√A)^2 ≤ ε^2` since `(m+n)/A ≤ 1` and `ε^2 ≥ 0`.
      have hsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
      have hle : ((m + n : ℕ) : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.le_succ (m + n))
      have hratio : ((m + n : ℕ) : ℝ) / A ≤ (1 : ℝ) :=
        (div_le_one hApos).2 hle
      have hεsq : 0 ≤ (ε ^ (2 : ℕ)) := by nlinarith
      -- Rewrite `δ^2 = ε^2 / A` and finish by monotonicity of multiplication.
      have hδsq : δ ^ (2 : ℕ) = (ε ^ (2 : ℕ)) / A := by
        dsimp [δ]
        -- `((ε/√A)^2) = ε^2 / (√A)^2 = ε^2 / A`.
        have hsqrt_sq : (Real.sqrt A) ^ (2 : ℕ) = A := by
          -- `pow_two` variant of `sq_sqrt`.
          simpa [pow_two] using (Real.sq_sqrt (le_of_lt hApos))
        simpa [div_pow, hsqrt_sq]
      -- Now compare with `ε^2 * ((m+n)/A)`.
      calc
        ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) =
            ((m + n : ℕ) : ℝ) * ((ε ^ (2 : ℕ)) / A) := by simp [hδsq]
        _ = (ε ^ (2 : ℕ)) * (((m + n : ℕ) : ℝ) / A) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ (ε ^ (2 : ℕ)) * 1 := by
          exact mul_le_mul_of_nonneg_left hratio hεsq
        _ = ε ^ (2 : ℕ) := by simp
    -- Apply Chapter 24 to the `u`-slice convex functions to get eventual subdifferential inclusion.
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let fSeq : ℕ → (Fin m → ℝ) → EReal :=
      fun i x => if x ∈ C then ((-(KSeq i x (vSeq i)) : ℝ) : EReal) else (⊤ : EReal)
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    let gSeq : ℕ → (Fin n → ℝ) → EReal :=
      fun i y => if y ∈ D then ((KSeq i (uSeq i) y : ℝ) : EReal) else (⊤ : EReal)
    have hf_convOn : ConvexOn ℝ C (fun x => (-(K x v) : ℝ)) := by
      -- Avoid `simp` rewriting `ConvexOn (-f)` to a `ConcaveOn f` goal.
      exact (hK.1 v hv).neg
    have hf : ConvexFunction f :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (s := C) (f := fun x => (-(K x v) : ℝ))
        hf_convOn).1
    have hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
      intro z hz
      simp [f, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ C (fun x => (-(KSeq i x (vSeq i)) : ℝ)) := by
        -- Avoid `simp` rewriting `ConvexOn (-f)` to a `ConcaveOn f` goal.
        exact ((hKSeq i).1 (vSeq i) (hvSeq i)).neg
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (s := C) (f := fun x => (-(KSeq i x (vSeq i)) : ℝ)) hconvOn).1
    have hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [fSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_f : ∀ z ∈ C, Filter.Tendsto (fun i : ℕ => fSeq i z) Filter.atTop (nhds (f z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i z (vSeq i)) Filter.atTop (nhds (K z v)) :=
        hpoint_uSlices z hz
      simpa [f, fSeq, hz] using (helperForTheorem_5_24_8_tendsto_coe_of_tendsto (hu := hzT.neg))
    have hChapU :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := C) hC_open hC_conv hf hf_finite fSeq hfSeq hfSeq_finite hu uSeq huSeq huSeq_tendsto
        hpoint_f
    have hsubU := hChapU.2 δ hδpos
    -- Apply Chapter 24 to the `v`-slice convex functions.
    have hg_convOn : ConvexOn ℝ D (fun y => (K u y : ℝ)) := (hK.2 u hu)
    have hg : ConvexFunction g :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (s := D) (f := fun y => (K u y : ℝ))
        hg_convOn).1
    have hg_finite : ∀ z ∈ D, g z ≠ (⊤ : EReal) ∧ g z ≠ (⊥ : EReal) := by
      intro z hz
      simp [g, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hgSeq : ∀ i, ConvexFunction (gSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ D (fun y => (KSeq i (uSeq i) y : ℝ)) := (hKSeq i).2 (uSeq i) (huSeq i)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (s := D) (f := fun y => (KSeq i (uSeq i) y : ℝ)) hconvOn).1
    have hgSeq_finite : ∀ i, ∀ z ∈ D, gSeq i z ≠ (⊤ : EReal) ∧ gSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [gSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_g : ∀ z ∈ D, Filter.Tendsto (fun i : ℕ => gSeq i z) Filter.atTop (nhds (g z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) z) Filter.atTop (nhds (K u z)) :=
        hpoint_vSlices z hz
      simpa [g, gSeq, hz] using (helperForTheorem_5_24_8_tendsto_coe_of_tendsto hzT)
    have hChapV :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := D) hD_open hD_conv hg hg_finite gSeq hgSeq hgSeq_finite hv vSeq hvSeq hvSeq_tendsto
        hpoint_g
    have hsubV := hChapV.2 δ hδpos
    -- Combine the two coordinatewise inclusions, then translate back to the saddle subdifferential.
    rcases hsubU with ⟨iU, hiU⟩
    rcases hsubV with ⟨iV, hiV⟩
    refine ⟨max iU iV, ?_⟩
    intro i hi
    have hiU' : i ≥ iU := le_trans (le_max_left _ _) hi
    have hiV' : i ≥ iV := le_trans (le_max_right _ _) hi
    have hBridgeK :=
      (helperForTheorem_35_7_realPartialSubdifferential_bridges (C := C) (D := D) (K := K) (u := u) (v := v) hu hv)
    have hBridgeKi :=
      (helperForTheorem_35_7_realPartialSubdifferential_bridges
        (C := C) (D := D) (K := KSeq i) (u := uSeq i) (v := vSeq i) (hu := huSeq i) (hv := hvSeq i))
    intro p hp
    rcases hp with ⟨huStar, hvStar⟩
    -- Move to the one-variable subdifferentials using the bridge, apply the Chapter 24 inclusions,
    -- then move back and package the errors into the split ball.
    have hAu :
        dotProductEquiv ℝ (Fin m) (-p.1) ∈ subdifferentialAt (fSeq i) (uSeq i) := by
      -- The bridge lemma uses `dotProductEquiv (-uStar)` for a real partial subgradient `uStar`.
      exact (hBridgeKi.1 p.1).1 huStar
    have hAv :
        dotProductEquiv ℝ (Fin n) p.2 ∈ subdifferentialAt (gSeq i) (vSeq i) := by
      exact (hBridgeKi.2 p.2).1 hvStar
    have hAuMem :
        (-p.1) ∈ (⇑(dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fSeq i) (uSeq i)) := by
      -- This is definitional: membership in a preimage is membership after applying the map.
      simpa [Set.preimage] using hAu
    have hAvMem :
        p.2 ∈ (⇑(dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (gSeq i) (vSeq i)) := by
      simpa [Set.preimage] using hAv
    have hAuInc := (hiU i hiU') hAuMem
    have hAvInc := (hiV i hiV') hAvMem
    rcases hAuInc with ⟨u0, hu0, du, hdu, hsumu⟩
    rcases hAvInc with ⟨v0, hv0, dv, hdv, hsumv⟩
    have hu0' : (-u0) ∈ realPartialSubdifferentialInFirstVariableOn C K u v := by
      have : dotProductEquiv ℝ (Fin m) (-(-u0)) ∈ subdifferentialAt f u := by
        simpa using hu0
      simpa using (hBridgeK.1 (-u0)).2 this
    have hv0' : v0 ∈ realPartialSubdifferentialInSecondVariableOn D K u v := by
      have : dotProductEquiv ℝ (Fin n) v0 ∈ subdifferentialAt g v := by
        simpa using hv0
      simpa using (hBridgeK.2 v0).2 this
    have hdu' : ‖du‖ ≤ δ := by
      -- `hdu` is a membership proof in `{v | ‖v‖ ≤ δ}`.
      simpa using hdu
    have hduNeg : ‖-du‖ ≤ δ := by
      -- The split-ball lemma is stated using `‖-du‖`; this is the same as `‖du‖`.
      simpa [norm_neg] using hdu'
    have hball :
        ((-du, dv) : (Fin m → ℝ) × (Fin n → ℝ)) ∈ splitEuclideanClosedBall (m := m) (n := n) ε :=
      helperForTheorem_35_7_splitBall_combine_errors (m := m) (n := n) (ε := ε) (δ := δ)
        hδnonneg hδineq hduNeg hdv
    refine ⟨((-u0, v0) : (Fin m → ℝ) × (Fin n → ℝ)), ?_, ((-du, dv) : (Fin m → ℝ) × (Fin n → ℝ)), hball, ?_⟩
    · exact ⟨hu0', hv0'⟩
    · -- Use the equalities from Chapter 24 and simplify the resulting sum.
      have hsumu' : u0 + du = -p.1 := by
        simpa using hsumu
      have hsumv' : v0 + dv = p.2 := by
        simpa using hsumv
      ext x
      · -- First coordinate: `u0 + du = -p.1` implies `(-u0) + (-du) = p.1` after negating.
        have hsumu_x : u0 x + du x = -(p.1 x) := by
          have : (u0 + du) x = (-p.1) x := congrArg (fun w => w x) hsumu'
          simpa [Pi.add_apply, Pi.neg_apply] using this
        -- Expand the product addition and evaluation, then compute using `hsumu_x`.
        dsimp
        -- Now the goal is `(-u0 x) + (-du x) = p.1 x`.
        calc
          (-u0 x) + (-du x) = -(u0 x + du x) := by
            simpa using (neg_add (u0 x) (du x)).symm
          _ = -(-(p.1 x)) := by simpa [hsumu_x]
          _ = p.1 x := by simp
      · -- Second coordinate: `v0 + dv = p.2` is already in the desired form.
        have : (v0 + dv) x = p.2 x := congrArg (fun w => w x) hsumv'
        have hsumv_x : v0 x + dv x = p.2 x := by
          simpa [Pi.add_apply] using this
        dsimp
        -- Now the goal is `v0 x + dv x = p.2 x`.
        simpa using hsumv_x

  exact ⟨hFirstIneq, hSecondIneq, hEventuallySubdiff⟩
  /-
  -- Step 1: obtain the moving-slice pointwise convergence needed for Chapter 24.
  rcases
      helperForTheorem_35_7_pointwiseTendsto_movingSlices
        (C := C) (D := D) (K := K) (KSeq := KSeq)
        hC_open hD_open hC_conv hD_conv hKSeq hpoint hu hv
        uSeq vSeq huSeq hvSeq huSeq_tendsto hvSeq_tendsto with
    ⟨hpoint_uSlices, hpoint_vSlices⟩

  -- Step 2: prove the first-variable liminf inequality via Chapter 24 on the convex slices
  -- `x ↦ if x∈C then -(K x v) else ⊤` and `x ↦ if x∈C then -(KSeq i x (vSeq i)) else ⊤`.
  have hFirstIneq :
      ∀ u' : Fin m → ℝ,
        ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) ≤
          Filter.liminf
            (fun i : ℕ =>
              ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
                EReal))
            Filter.atTop := by
    intro u'
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let fSeq : ℕ → (Fin m → ℝ) → EReal :=
      fun i x => if x ∈ C then ((-(KSeq i x (vSeq i)) : ℝ) : EReal) else (⊤ : EReal)
    have hf_convOn : ConvexOn ℝ C (fun x => -K x v) := by
      simpa using (hK.1 v hv).neg
    have hf : ConvexFunction f :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (f := fun x => -K x v)
        hf_convOn).1
    have hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
      intro z hz
      simp [f, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ C (fun x => -KSeq i x (vSeq i)) := by
        simpa using (((hKSeq i).1 (vSeq i) (hvSeq i)).neg)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (f := fun x => -KSeq i x (vSeq i)) hconvOn).1
    have hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [fSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_f : ∀ z ∈ C, Filter.Tendsto (fun i : ℕ => fSeq i z) Filter.atTop (nhds (f z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i z (vSeq i)) Filter.atTop (nhds (K z v)) :=
        hpoint_uSlices z hz
      -- Negation and coercion transport the pointwise convergence.
      simpa [f, fSeq, hz, EReal.coe_neg] using hzT.neg
    have hChapter24 :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := C) hC_open hC_conv hf hf_finite fSeq hfSeq hfSeq_finite hu uSeq huSeq huSeq_tendsto
        hpoint_f
    have hLimsup :
        Filter.limsup (fun i : ℕ => upperDirectionalDerivativeAt (fSeq i) (uSeq i) u')
            Filter.atTop ≤ upperDirectionalDerivativeAt f u u' := by
      simpa using hChapter24.1 u' (fun _ : ℕ => u')
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => u') Filter.atTop (nhds u'))
    -- Rewrite the upper-directional derivatives using the bridge lemma, then convert the
    -- resulting limsup inequality to the desired liminf inequality via `EReal.limsup_neg`.
    have hbridgeLimit :
        ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) =
          -upperDirectionalDerivativeAt f u u' := by
      simpa [f] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv u' (0 : Fin n → ℝ)).1
    have hbridgeSeq :
        ∀ i : ℕ,
          ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) : EReal) =
            -upperDirectionalDerivativeAt (fSeq i) (uSeq i) u' := by
      intro i
      simpa [fSeq] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := KSeq i) hC_open hD_open hC_conv hD_conv (hKSeq i)
          (huSeq i) (hvSeq i) u' (0 : Fin n → ℝ)).1
    have hLimsup' :
        Filter.limsup
            (fun i : ℕ =>
              -((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
                EReal))
            Filter.atTop ≤
          -((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) := by
      -- Substitute the bridge equalities into the Chapter 24 inequality.
      have : Filter.limsup (fun i : ℕ => upperDirectionalDerivativeAt (fSeq i) (uSeq i) u')
              Filter.atTop ≤ upperDirectionalDerivativeAt f u u' := hLimsup
      -- Rewrite both sides.
      simpa [hbridgeLimit, hbridgeSeq] using this
    have hNeg :
        -Filter.liminf
            (fun i : ℕ =>
              ((realFirstVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) u' : ℝ) :
                EReal))
            Filter.atTop ≤
          -((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) := by
      -- `limsup (-a_i) = - liminf a_i`.
      simpa [EReal.limsup_neg] using hLimsup'
    exact (neg_le_neg_iff).1 hNeg

  -- Step 3: prove the second-variable limsup inequality similarly.
  have hSecondIneq :
      ∀ v' : Fin n → ℝ,
        Filter.limsup
            (fun i : ℕ =>
              ((realSecondVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) v' : ℝ) :
                EReal))
            Filter.atTop ≤
          ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) := by
    intro v'
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    let gSeq : ℕ → (Fin n → ℝ) → EReal :=
      fun i y => if y ∈ D then ((KSeq i (uSeq i) y : ℝ) : EReal) else (⊤ : EReal)
    have hg_convOn : ConvexOn ℝ D (K u) := (hK.2 u hu)
    have hg : ConvexFunction g :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (f := fun y => K u y)
        hg_convOn).1
    have hg_finite : ∀ z ∈ D, g z ≠ (⊤ : EReal) ∧ g z ≠ (⊥ : EReal) := by
      intro z hz
      simp [g, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hgSeq : ∀ i, ConvexFunction (gSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ D (KSeq i (uSeq i)) := (hKSeq i).2 (uSeq i) (huSeq i)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (f := fun y => KSeq i (uSeq i) y) hconvOn).1
    have hgSeq_finite : ∀ i, ∀ z ∈ D, gSeq i z ≠ (⊤ : EReal) ∧ gSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [gSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_g : ∀ z ∈ D, Filter.Tendsto (fun i : ℕ => gSeq i z) Filter.atTop (nhds (g z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) z) Filter.atTop (nhds (K u z)) :=
        hpoint_vSlices z hz
      simpa [g, gSeq, hz] using (hzT.map (continuous_coe : Continuous fun r : ℝ => (r : EReal)))
    have hChapter24 :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := D) hD_open hD_conv hg hg_finite gSeq hgSeq hgSeq_finite hv vSeq hvSeq hvSeq_tendsto
        hpoint_g
    have hLimsup :
        Filter.limsup (fun i : ℕ => upperDirectionalDerivativeAt (gSeq i) (vSeq i) v')
            Filter.atTop ≤ upperDirectionalDerivativeAt g v v' := by
      simpa using hChapter24.1 v' (fun _ : ℕ => v')
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => v') Filter.atTop (nhds v'))
    -- Rewrite using bridges.
    have hbridgeLimit :
        ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) =
          upperDirectionalDerivativeAt g v v' := by
      simpa [g] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv (0 : Fin m → ℝ) v').2
    have hbridgeSeq :
        ∀ i : ℕ,
          ((realSecondVariableDirectionalDerivativeValue (KSeq i) (uSeq i) (vSeq i) v' : ℝ) : EReal) =
            upperDirectionalDerivativeAt (gSeq i) (vSeq i) v' := by
      intro i
      simpa [gSeq] using
        (helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
          (C := C) (D := D) (K := KSeq i) hC_open hD_open hC_conv hD_conv (hKSeq i)
          (huSeq i) (hvSeq i) (0 : Fin m → ℝ) v').2
    simpa [hbridgeLimit, hbridgeSeq] using hLimsup

  -- Step 4: prove the eventual saddle-subdifferential inclusion by combining the two one-variable
  -- Chapter 24 subdifferential inclusions and packaging the product error in `splitEuclideanClosedBall`.
  have hEventuallySubdiff :
      ∀ ε : ℝ, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        realSaddleSubdifferentialOn C D (KSeq i) (uSeq i) (vSeq i) ⊆
          Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
            (realSaddleSubdifferentialOn C D K u v)
            (splitEuclideanClosedBall (m := m) (n := n) ε) := by
    intro ε hε
    -- Choose a smaller one-variable tolerance `δ` so that `(δ,δ)`-errors lie in the split ball.
    let A : ℝ := ((m + n + 1 : ℕ) : ℝ)
    let δ : ℝ := ε / Real.sqrt A
    have hApos : 0 < A := by
      have : 0 < (m + n + 1 : ℕ) := Nat.succ_pos _
      exact_mod_cast this
    have hδpos : 0 < δ := by
      have hsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
      exact div_pos hε hsqrtpos
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hδineq : ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by
      -- `(m+n) * (ε/√A)^2 ≤ ε^2` since `(m+n)/A ≤ 1`.
      simp [δ, pow_two]
      have hApos' : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
      have hsq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt (le_of_lt hApos)
      -- Reduce to `(m+n)/A ≤ 1`.
      have hratio : ((m + n : ℕ) : ℝ) / A ≤ (1 : ℝ) := by
        have hle : ((m + n : ℕ) : ℝ) ≤ A := by
          -- `m+n ≤ m+n+1`.
          exact_mod_cast (Nat.le_succ (m + n))
        exact (div_le_one hApos).2 hle
      have hεsq : 0 ≤ ε ^ (2 : ℕ) := by nlinarith
      nlinarith [hratio, hεsq, hsq]
    -- Build the u-slice convex functions and apply Chapter 24 to get eventual inclusion.
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let fSeq : ℕ → (Fin m → ℝ) → EReal :=
      fun i x => if x ∈ C then ((-(KSeq i x (vSeq i)) : ℝ) : EReal) else (⊤ : EReal)
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    let gSeq : ℕ → (Fin n → ℝ) → EReal :=
      fun i y => if y ∈ D then ((KSeq i (uSeq i) y : ℝ) : EReal) else (⊤ : EReal)
    have hf_convOn : ConvexOn ℝ C (fun x => -K x v) := by
      simpa using (hK.1 v hv).neg
    have hf : ConvexFunction f :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (f := fun x => -K x v)
        hf_convOn).1
    have hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := by
      intro z hz
      simp [f, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hfSeq : ∀ i, ConvexFunction (fSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ C (fun x => -KSeq i x (vSeq i)) := by
        simpa using (((hKSeq i).1 (vSeq i) (hvSeq i)).neg)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (f := fun x => -KSeq i x (vSeq i)) hconvOn).1
    have hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [fSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_f : ∀ z ∈ C, Filter.Tendsto (fun i : ℕ => fSeq i z) Filter.atTop (nhds (f z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i z (vSeq i)) Filter.atTop (nhds (K z v)) :=
        hpoint_uSlices z hz
      simpa [f, fSeq, hz, EReal.coe_neg] using hzT.neg
    have hChapU :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := C) hC_open hC_conv hf hf_finite fSeq hfSeq hfSeq_finite hu uSeq huSeq huSeq_tendsto
        hpoint_f
    have hsubU := hChapU.2 δ hδpos
    -- Apply Chapter 24 to the v-slice convex functions.
    have hg_convOn : ConvexOn ℝ D (K u) := (hK.2 u hu)
    have hg : ConvexFunction g :=
      (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn (f := fun y => K u y)
        hg_convOn).1
    have hg_finite : ∀ z ∈ D, g z ≠ (⊤ : EReal) ∧ g z ≠ (⊥ : EReal) := by
      intro z hz
      simp [g, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hgSeq : ∀ i, ConvexFunction (gSeq i) := by
      intro i
      have hconvOn : ConvexOn ℝ D (KSeq i (uSeq i)) := (hKSeq i).2 (uSeq i) (huSeq i)
      exact
        (helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
          (f := fun y => KSeq i (uSeq i) y) hconvOn).1
    have hgSeq_finite : ∀ i, ∀ z ∈ D, gSeq i z ≠ (⊤ : EReal) ∧ gSeq i z ≠ (⊥ : EReal) := by
      intro i z hz
      simp [gSeq, hz, EReal.coe_ne_top, EReal.coe_ne_bot]
    have hpoint_g : ∀ z ∈ D, Filter.Tendsto (fun i : ℕ => gSeq i z) Filter.atTop (nhds (g z)) := by
      intro z hz
      have hzT :
          Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) z) Filter.atTop (nhds (K u z)) :=
        hpoint_vSlices z hz
      simpa [g, gSeq, hz] using (hzT.map (continuous_coe : Continuous fun r : ℝ => (r : EReal)))
    have hChapV :=
      convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
        (C := D) hD_open hD_conv hg hg_finite gSeq hgSeq hgSeq_finite hv vSeq hvSeq hvSeq_tendsto
        hpoint_g
    have hsubV := hChapV.2 δ hδpos
    -- Combine the two eventual inclusions, then translate using the partial-subdifferential bridges.
    rcases hsubU with ⟨iU, hiU⟩
    rcases hsubV with ⟨iV, hiV⟩
    refine ⟨max iU iV, ?_⟩
    intro i hi
    have hiU' : i ≥ iU := le_trans (le_max_left _ _) hi
    have hiV' : i ≥ iV := le_trans (le_max_right _ _) hi
    -- Bridge lemmas for `K` and `KSeq i`.
    have hBridgeK :
        (∀ uStar : Fin m → ℝ,
            uStar ∈ realPartialSubdifferentialInFirstVariableOn C K u v ↔
              dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt f u) ∧
          (∀ vStar : Fin n → ℝ,
            vStar ∈ realPartialSubdifferentialInSecondVariableOn D K u v ↔
              dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt g v) := by
      simpa [f, g] using
        helperForTheorem_35_7_realPartialSubdifferential_bridges (C := C) (D := D) (K := K) hu hv
    have hBridgeKi :
        (∀ uStar : Fin m → ℝ,
            uStar ∈ realPartialSubdifferentialInFirstVariableOn C (KSeq i) (uSeq i) (vSeq i) ↔
              dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt (fSeq i) (uSeq i)) ∧
          (∀ vStar : Fin n → ℝ,
            vStar ∈ realPartialSubdifferentialInSecondVariableOn D (KSeq i) (uSeq i) (vSeq i) ↔
              dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt (gSeq i) (vSeq i)) := by
      simpa [fSeq, gSeq] using
        helperForTheorem_35_7_realPartialSubdifferential_bridges
          (C := C) (D := D) (K := KSeq i) (hu := huSeq i) (hv := hvSeq i)
    -- Unpack the product saddle subdifferential and apply the two coordinate inclusions.
    intro p hp
    rcases hp with ⟨huStar, hvStar⟩
    -- First coordinate: use the Chapter 24 inclusion for `fSeq i` and transport through negation.
    have hAu :
        (-p.1) ∈ ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt (fSeq i) (uSeq i)) := by
      simpa [Set.preimage, hBridgeKi.1 p.1] using (hBridgeKi.1 p.1).1 huStar
    have hAuInclusion := (hiU i hiU') hAu
    rcases hAuInclusion with ⟨u0, hu0, du, hdu, rfl⟩
    have hu0' : (-u0) ∈ realPartialSubdifferentialInFirstVariableOn C K u v := by
      -- Use the bridge lemma backwards.
      have : dotProductEquiv ℝ (Fin m) (-(-u0)) ∈ subdifferentialAt f u := by
        simpa using hu0
      simpa using (hBridgeK.1 (-u0)).2 this
    have hdu' : ‖(-du : Fin m → ℝ)‖ ≤ δ := by simpa using hdu
    -- Second coordinate: apply the Chapter 24 inclusion for `gSeq i`.
    have hAv :
        p.2 ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (gSeq i) (vSeq i)) := by
      have : dotProductEquiv ℝ (Fin n) p.2 ∈ subdifferentialAt (gSeq i) (vSeq i) :=
        (hBridgeKi.2 p.2).1 hvStar
      simpa [Set.preimage] using this
    have hAvInclusion := (hiV i hiV') hAv
    rcases hAvInclusion with ⟨v0, hv0, dv, hdv, rfl⟩
    have hv0' : v0 ∈ realPartialSubdifferentialInSecondVariableOn D K u v := by
      have : dotProductEquiv ℝ (Fin n) v0 ∈ subdifferentialAt g v := by
        simpa using hv0
      simpa using (hBridgeK.2 v0).2 this
    -- Package the product element and the combined split-ball error.
    have hball :
        ((-du, dv) : (Fin m → ℝ) × (Fin n → ℝ)) ∈ splitEuclideanClosedBall (m := m) (n := n) ε :=
      helperForTheorem_35_7_splitBall_combine_errors (m := m) (n := n) (ε := ε) (δ := δ)
        hδnonneg hδineq hdu' hdv
    refine ⟨((-u0, v0) : (Fin m → ℝ) × (Fin n → ℝ)), ?_, ((-du, dv) : (Fin m → ℝ) × (Fin n → ℝ)), hball, ?_⟩
    · -- Membership in the limit saddle subdifferential is product membership.
      exact ⟨hu0', hv0'⟩
    · -- Componentwise addition gives the desired element.
      ext <;> simp [add_assoc, add_comm, add_left_comm]

  exact ⟨hFirstIneq, hSecondIneq, hEventuallySubdiff⟩
  -/

/-!
Helpers for Corollary 35.7.1.

The corollary is obtained from Theorem 35.7 by specializing to the constant sequence `Kᵢ = K`.
We then package the `liminf`/`limsup` inequalities as (lower/upper) semicontinuity on `C ×ˢ D`,
and repackage the eventual subdifferential inclusion as a uniform neighborhood statement.
-/

/-- Helper for Corollary 35.7.1: specialize Theorem 35.7 to the constant sequence `Kᵢ = K`. -/
lemma helperForCorollary_35_7_1_constantSequence_asymptotics
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (uSeq : ℕ → Fin m → ℝ) (vSeq : ℕ → Fin n → ℝ)
    (huSeq : ∀ i : ℕ, uSeq i ∈ C) (hvSeq : ∀ i : ℕ, vSeq i ∈ D)
    (huSeq_tendsto : Filter.Tendsto uSeq Filter.atTop (nhds u))
    (hvSeq_tendsto : Filter.Tendsto vSeq Filter.atTop (nhds v)) :
    (∀ u' : Fin m → ℝ,
        ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) ≤
          Filter.liminf
            (fun i : ℕ =>
              ((realFirstVariableDirectionalDerivativeValue K (uSeq i) (vSeq i) u' : ℝ) : EReal))
            Filter.atTop) ∧
      (∀ v' : Fin n → ℝ,
          Filter.limsup
              (fun i : ℕ =>
                ((realSecondVariableDirectionalDerivativeValue K (uSeq i) (vSeq i) v' : ℝ) :
                  EReal))
              Filter.atTop ≤
            ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        realSaddleSubdifferentialOn C D K (uSeq i) (vSeq i) ⊆
          Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
            (realSaddleSubdifferentialOn C D K u v)
            (splitEuclideanClosedBall (m := m) (n := n) ε) := by
  classical
  -- Apply Theorem 35.7 with `KSeq i = K`. Pointwise convergence is trivial for a constant sequence.
  have hpoint :
      ∀ u₀ ∈ C, ∀ v₀ ∈ D,
        Filter.Tendsto (fun _i : ℕ => K u₀ v₀) Filter.atTop (nhds (K u₀ v₀)) := by
    intro u₀ hu₀ v₀ hv₀
    simpa using (Filter.tendsto_const_nhds : Filter.Tendsto (fun _i : ℕ => K u₀ v₀) Filter.atTop
      (nhds (K u₀ v₀)))
  simpa using
    (section35_theorem35_7 (C := C) (D := D) (K := K) (KSeq := fun _i : ℕ => K)
      hC_open hD_open hC_conv hD_conv hK (fun _i : ℕ => hK) hpoint
      hu hv uSeq vSeq huSeq hvSeq huSeq_tendsto hvSeq_tendsto)


end Section35
end Chap07
