/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Example_5_3_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H}

/-- Helper for Theorem 5.14: every weak sequential cluster point of the Picard orbit lies in the
ambient image of the fixed-point set once the residuals tend to `0`. -/
private theorem weak_cluster_point_mem_fixedPoints_image_of_picard_residual
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (x₀ : D)
    (hres :
      Tendsto (fun n ↦ ((T^[n]) x₀ : H) - (T ((T^[n]) x₀) : H)) atTop (𝓝 (0 : H)))
    {z : H}
    (hz :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H ((T^[n]) x₀ : H))
        (toWeakSpace ℝ H z)) :
    z ∈ Subtype.val '' Function.fixedPoints T := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
  have hzD : z ∈ D := by
    -- Closed convexity keeps the weak limit of a Picard subsequence inside `D`.
    have hD_weakClosed : IsClosed ((toWeakSpace ℝ H) '' D) :=
      (isClosed_iff_weak_image_isClosed_of_convex hD_convex).1 hD_closed
    have hzWeak :
        toWeakSpace ℝ H z ∈ closure ((toWeakSpace ℝ H) '' D) := by
      exact mem_closure_of_tendsto hφz <|
        Filter.Eventually.of_forall fun n ↦ ⟨((T^[φ n]) x₀ : H), ((T^[φ n]) x₀).2, rfl⟩
    rw [hD_weakClosed.closure_eq] at hzWeak
    rcases hzWeak with ⟨y, hyD, hyz⟩
    exact (toWeakSpace ℝ H).injective hyz ▸ hyD
  let zD : D := ⟨z, hzD⟩
  have hres_sub :
      Tendsto
        (fun n ↦ ((T^[φ n]) x₀ : H) - (T ((T^[φ n]) x₀) : H))
        atTop (𝓝 (0 : H)) := by
    -- Residual decay persists after passage to the convergent subsequence.
    exact hres.comp hφ.tendsto_atTop
  have hz_fixed : T zD = (z : H) := by
    -- Demiclosedness turns the weak limit of approximate fixed points into a fixed point.
    have hφz' :
        Tendsto (fun n ↦ toWeakSpace ℝ H (((T^[φ n]) x₀ : D) : H)) atTop
          (𝓝 (toWeakSpace ℝ H (zD : H))) := by
      simpa [zD] using hφz
    simpa [zD] using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        (xₙ := fun n ↦ (T^[φ n]) x₀) (x := zD) hD_closed hD_convex hT hφz' hres_sub
  refine ⟨zD, ?_, rfl⟩
  rw [Function.mem_fixedPoints_iff]
  exact Subtype.ext hz_fixed

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 5.14: oddness of `T` propagates to every Picard iterate. -/
private theorem iterate_neg_eq_neg_iterate {T : D → D}
    (hD_symm : Set.MapsTo (fun x : H ↦ -x) D D)
    (hT_odd : ∀ x : D, (T ⟨-(x : H), hD_symm x.2⟩ : H) = -(T x : H))
    (n : ℕ) (x : D) :
    ((T^[n]) ⟨-(x : H), hD_symm x.2⟩ : H) = -((T^[n]) x : H) := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have hsub :
          (T^[n]) ⟨-(x : H), hD_symm x.2⟩ =
            ⟨-((T^[n]) x : H), hD_symm ((T^[n]) x).2⟩ :=
        Subtype.ext ihn
      -- Apply oddness at the `n`th iterate and rewrite the left branch through the induction step.
      calc
        ((T^[n + 1]) ⟨-(x : H), hD_symm x.2⟩ : H)
            = (T ((T^[n]) ⟨-(x : H), hD_symm x.2⟩) : H) := by
                simp [Function.iterate_succ_apply']
        _ = (T ⟨-((T^[n]) x : H), hD_symm ((T^[n]) x).2⟩ : H) := by
              rw [hsub]
        _ = -(T ((T^[n]) x) : H) := hT_odd ((T^[n]) x)
        _ = -((T^[n + 1]) x : H) := by
              simp [Function.iterate_succ_apply']

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 5.14: for each fixed shift `m`, the norms `‖x_{n+m} + x_n‖` decrease along
the Picard orbit of an odd nonexpansive map. -/
private theorem add_iterates_norm_antitone_of_odd {T : D → D}
    (hT : LipschitzWith 1 T)
    (hD_symm : Set.MapsTo (fun x : H ↦ -x) D D)
    (hT_odd : ∀ x : D, (T ⟨-(x : H), hD_symm x.2⟩ : H) = -(T x : H))
    (x₀ : D) (m : ℕ) :
    Antitone (fun n ↦ ‖((T^[n + m]) x₀ : H) + ((T^[n]) x₀ : H)‖) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  -- Rewrite the odd iterate pair as a nonexpansive comparison between `x_{n+m}` and `-x_n`.
  let xn : D := (T^[n]) x₀
  let xnm : D := (T^[n + m]) x₀
  have hleft :
      dist (T ⟨-(xn : H), hD_symm xn.2⟩) (T xnm) =
        ‖((T^[(n + 1) + m]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖ := by
    calc
      dist (T ⟨-(xn : H), hD_symm xn.2⟩) (T xnm)
          = ‖(T ⟨-(xn : H), hD_symm xn.2⟩ : H) - (T xnm : H)‖ := by
              simp [Subtype.dist_eq, dist_eq_norm]
      _ = ‖-((T xn : H)) - (T xnm : H)‖ := by
            rw [hT_odd xn]
      _ = ‖-(((T xnm : H) + (T xn : H)) : H)‖ := by
            congr 1
            abel_nf
      _ = ‖((T xnm : H) + (T xn : H))‖ := by
            rw [norm_neg]
      _ = ‖((T^[(n + 1) + m]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖ := by
            calc
              ‖((T xnm : H) + (T xn : H))‖ = ‖((T^[(n + m) + 1]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖ := by
                  simp [xn, xnm, Function.iterate_succ_apply']
              _ = ‖((T^[n + m + 1]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖ := by
                  simp
              _ = ‖((T^[(n + 1) + m]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖ := by
                  congr 1
                  simp [Nat.add_assoc, Nat.add_comm]
  have hright :
      dist ⟨-(xn : H), hD_symm xn.2⟩ xnm =
        ‖((T^[n + m]) x₀ : H) + ((T^[n]) x₀ : H)‖ := by
    calc
      dist ⟨-(xn : H), hD_symm xn.2⟩ xnm
          = ‖(-(xn : H)) - (xnm : H)‖ := by
              simp [Subtype.dist_eq, dist_eq_norm]
      _ = ‖-(((xnm : H) + (xn : H)) : H)‖ := by
            congr 1
            abel_nf
      _ = ‖((xnm : H) + (xn : H))‖ := by
            rw [norm_neg]
      _ = ‖((T^[n + m]) x₀ : H) + ((T^[n]) x₀ : H)‖ := by
            simp [xn, xnm]
  have hdist :
      dist (T ⟨-(xn : H), hD_symm xn.2⟩) (T xnm) ≤ dist ⟨-(xn : H), hD_symm xn.2⟩ xnm := by
    simpa [one_mul] using hT.dist_le_mul ⟨-(xn : H), hD_symm xn.2⟩ xnm
  calc
    ‖((T^[(n + 1) + m]) x₀ : H) + ((T^[n + 1]) x₀ : H)‖
        = dist (T ⟨-(xn : H), hD_symm xn.2⟩) (T xnm) := hleft.symm
    _ ≤ dist ⟨-(xn : H), hD_symm xn.2⟩ xnm := hdist
    _ = ‖((T^[n + m]) x₀ : H) + ((T^[n]) x₀ : H)‖ := hright

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 5.14: asymptotic regularity of the Picard orbit implies that every fixed
shift difference `x_{n+m} - x_n` tends strongly to `0`. -/
private theorem shifted_iterate_difference_tendsto_zero_of_residual_tendsto_zero
    {T : D → D} (x₀ : D)
    (hres :
      Tendsto (fun n ↦ ((T^[n]) x₀ : H) - (T ((T^[n]) x₀) : H)) atTop (𝓝 (0 : H)))
    (m : ℕ) :
    Tendsto (fun n ↦ ((T^[n + m]) x₀ : H) - ((T^[n]) x₀ : H)) atTop (𝓝 (0 : H)) := by
  induction m with
  | zero =>
      -- The zero shift gives the constant zero sequence.
      simp
  | succ m ihm =>
      have hstep :
          Tendsto
            (fun n ↦ ((T^[n + 1]) x₀ : H) - ((T^[n]) x₀ : H))
            atTop (𝓝 (0 : H)) := by
        -- Negating the residual rewrites it as the one-step Picard increment.
        simpa [Function.iterate_succ_apply', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hres.neg
      have hshift :
          Tendsto
            (fun n ↦ ((T^[(n + 1) + m]) x₀ : H) - ((T^[n + 1]) x₀ : H))
            atTop (𝓝 (0 : H)) := by
        exact ihm.comp (tendsto_add_atTop_nat 1)
      have hsplit :
          (fun n ↦ ((T^[n + (m + 1)]) x₀ : H) - ((T^[n]) x₀ : H)) =
            (fun n ↦
              (((T^[(n + 1) + m]) x₀ : H) - ((T^[n + 1]) x₀ : H)) +
                (((T^[n + 1]) x₀ : H) - ((T^[n]) x₀ : H))) := by
        funext n
        simp [Nat.add_left_comm, Nat.add_comm]
      -- Split the `(m + 1)`-shift into the shifted `m`-difference plus one increment.
      simpa [hsplit] using hshift.add hstep

-- Proof sketch: Example 5.3 makes the Picard orbit `n ↦ (T^[n]) x₀` Fejér monotone with respect
-- to `Function.fixedPoints T`. Every weak sequential cluster point is a fixed point by Corollary
-- 4.28, applied to the asymptotic-regularity hypothesis `xₙ - T xₙ → 0`. Then Theorem 5.5 yields
-- weak convergence of the whole orbit to a point of `Function.fixedPoints T`.
/-- Theorem 5.14 (1): (i) if a nonexpansive self-map of a nonempty closed convex subset has a
nonempty fixed-point set and its Picard residuals converge strongly to `0`, then its Picard
iterates converge weakly to a fixed point. -/
theorem tendsto_weakly_iterates_to_fixedPoint_of_residual_tendsto_zero_of_nonexpansive
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hFix : (Function.fixedPoints T).Nonempty) (x₀ : D)
    (hres :
      Tendsto (fun n ↦ ((T^[n]) x₀ : H) - (T ((T^[n]) x₀) : H)) atTop (𝓝 (0 : H))) :
    ∃ z ∈ Function.fixedPoints T,
      Tendsto (fun n ↦ toWeakSpace ℝ H ((T^[n]) x₀ : H)) atTop
        (𝓝 (toWeakSpace ℝ H (z : H))) := by
  have hquasi : IsQuasinonexpansiveOn (fun x : D ↦ (T x : H)) := by
    intro x y hy
    -- A `1`-Lipschitz self-map is quasinonexpansive against each fixed point.
    have hxy : ‖(T x : H) - (T y : H)‖ ≤ ‖(x : H) - y‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT.dist_le_mul x y
    have hxy' : ‖(T x : H) - y‖ ≤ ‖(x : H) - y‖ := by
      simpa [hy] using hxy
    simpa [dist_eq_norm] using hxy'
  have hfejer :
      FejerMonotone (Subtype.val '' Function.fixedPoints T) (fun n ↦ ((T^[n]) x₀ : H)) :=
    quasinonexpansive_iterates_fejer_monotone T hquasi x₀
  have hFix_image : (Subtype.val '' Function.fixedPoints T).Nonempty := by
    rcases hFix with ⟨z, hz⟩
    exact ⟨z, ⟨z, hz, rfl⟩⟩
  rcases
      tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem
        hFix_image (fun n ↦ ((T^[n]) x₀ : H)) hfejer
        (fun z hz ↦
          weak_cluster_point_mem_fixedPoints_image_of_picard_residual
            hD_closed hD_convex hT x₀ hres hz) with
    ⟨z, hz, hweak⟩
  rcases hz with ⟨zD, hzD, rfl⟩
  exact ⟨zD, hzD, hweak⟩

-- Proof sketch: symmetry of `D` and convexity imply `0 ∈ D`, and oddness of `T` then gives
-- `0 ∈ Function.fixedPoints T`, so the norms of the iterates decrease. Applying oddness to the
-- shifted pair
-- `(x_{n + m}, -x_n)` yields the monotonicity of `‖x_{n+m} + x_n‖`; combined with the
-- parallelogram identity and the residual convergence, this makes the orbit Cauchy. Since `D` is
-- closed, the strong limit lies in `D`, and continuity of the nonexpansive map forces it to be a
-- fixed point.
/-- Theorem 5.14 (2): (ii) if moreover `D` is symmetric and `T` is odd, then the Picard iterates
converge strongly to a fixed point. -/
theorem tendsto_iterates_to_fixedPoint_of_residual_tendsto_zero_of_nonexpansive_of_symmetric_of_odd
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (x₀ : D)
    (hres :
      Tendsto (fun n ↦ ((T^[n]) x₀ : H) - (T ((T^[n]) x₀) : H)) atTop (𝓝 (0 : H)))
    (hD_symm : Set.MapsTo (fun x : H ↦ -x) D D)
    (hT_odd : ∀ x : D, (T ⟨-(x : H), hD_symm x.2⟩ : H) = -(T x : H)) :
    ∃ z ∈ Function.fixedPoints T,
      Tendsto (fun n ↦ ((T^[n]) x₀ : H)) atTop (𝓝 (z : H)) := by
  let x : ℕ → H := fun n ↦ ((T^[n]) x₀ : H)
  have hzeroD : (0 : H) ∈ D := by
    have hnegx₀ : -(x₀ : H) ∈ D := hD_symm x₀.2
    -- Convexity of the symmetric set places the midpoint of `x₀` and `-x₀` at the origin.
    simpa using
      hD_convex x₀.2 hnegx₀
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  let zeroD : D := ⟨0, hzeroD⟩
  have hzero_fixed_val : (T zeroD : H) = 0 := by
    have hodd_zero : (T zeroD : H) = -((T zeroD : H)) := by
      simpa [zeroD] using hT_odd zeroD
    have htwo : (2 : ℝ) • (T zeroD : H) = 0 := by
      simpa [two_smul] using eq_neg_iff_add_eq_zero.mp hodd_zero
    exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  have hzero_fixed : zeroD ∈ Function.fixedPoints T := by
    rw [Function.mem_fixedPoints_iff]
    exact Subtype.ext hzero_fixed_val
  have hquasi : IsQuasinonexpansiveOn (fun y : D ↦ (T y : H)) := by
    intro y z hz
    -- The nonexpansive Picard map is again quasinonexpansive against any fixed point.
    have hyz : ‖(T y : H) - (T z : H)‖ ≤ ‖(y : H) - z‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT.dist_le_mul y z
    have hyz' : ‖(T y : H) - z‖ ≤ ‖(y : H) - z‖ := by
      simpa [hz] using hyz
    simpa [dist_eq_norm] using hyz'
  have hfejer :
      FejerMonotone (Subtype.val '' Function.fixedPoints T) (fun n ↦ x n) :=
    quasinonexpansive_iterates_fejer_monotone T hquasi x₀
  have hnorm_step : ∀ n, ‖x (n + 1)‖ ≤ ‖x n‖ := by
    intro n
    -- Fejér monotonicity at the fixed point `0` gives the monotonic decay of `‖x_n‖`.
    simpa [x, dist_eq_norm] using hfejer 0 ⟨zeroD, hzero_fixed, rfl⟩ n
  have hnorm_antitone : Antitone (fun n ↦ ‖x n‖) :=
    antitone_nat_of_succ_le hnorm_step
  have hnorm_bddBelow : BddBelow (Set.range fun n ↦ ‖x n‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _
  let ℓ : ℝ := ⨅ n, ‖x n‖
  have hℓ_tendsto : Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 ℓ) := by
    simpa [ℓ] using tendsto_atTop_ciInf hnorm_antitone hnorm_bddBelow
  have hℓ_nonneg : 0 ≤ ℓ := by
    -- Nonnegativity of the whole norm sequence passes to its limit.
    refine le_ciInf ?_
    intro n
    exact norm_nonneg _
  have hℓ_le_norm : ∀ n, ℓ ≤ ‖x n‖ := by
    intro n
    -- An antitone convergent real sequence stays above its limit.
    exact ciInf_le hnorm_bddBelow n
  have hdiff_sq_le :
      ∀ n m : ℕ, ‖x (n + m) - x n‖ ^ 2 ≤ 4 * ‖x n‖ ^ 2 - 4 * ℓ ^ 2 := by
    intro n m
    have hsum_antitone :
        Antitone (fun k ↦ ‖x (k + m) + x k‖) :=
      add_iterates_norm_antitone_of_odd hT hD_symm hT_odd x₀ m
    have hsum_sq_antitone :
        Antitone (fun k ↦ ‖x (k + m) + x k‖ ^ 2) := by
      intro i j hij
      nlinarith [hsum_antitone hij, norm_nonneg (x (i + m) + x i), norm_nonneg (x (j + m) + x j)]
    have hdiff_m :
        Tendsto (fun k ↦ x (k + m) - x k) atTop (𝓝 (0 : H)) :=
      shifted_iterate_difference_tendsto_zero_of_residual_tendsto_zero x₀ hres m
    have hnorm_sq :
        Tendsto (fun k ↦ ‖x k‖ ^ 2) atTop (𝓝 (ℓ ^ 2)) := by
      simpa using hℓ_tendsto.pow 2
    have hnorm_shift_sq :
        Tendsto (fun k ↦ ‖x (k + m)‖ ^ 2) atTop (𝓝 (ℓ ^ 2)) := by
      simpa using (hℓ_tendsto.comp (tendsto_add_atTop_nat m)).pow 2
    have hdiff_sq :
        Tendsto (fun k ↦ ‖x (k + m) - x k‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using hdiff_m.norm.pow 2
    have hsum_sq_tendsto :
        Tendsto (fun k ↦ ‖x (k + m) + x k‖ ^ 2) atTop
          (𝓝 (2 * (ℓ ^ 2 + ℓ ^ 2))) := by
      have hrewrite :
          (fun k ↦ ‖x (k + m) + x k‖ ^ 2) =
            (fun k ↦ 2 * (‖x (k + m)‖ ^ 2 + ‖x k‖ ^ 2) - ‖x (k + m) - x k‖ ^ 2) := by
        funext k
        nlinarith [parallelogram_law_with_norm (𝕜 := ℝ) (x (k + m)) (x k)]
      have haux :
          Tendsto
            (fun k ↦ 2 * (‖x (k + m)‖ ^ 2 + ‖x k‖ ^ 2) - ‖x (k + m) - x k‖ ^ 2)
            atTop (𝓝 (2 * (ℓ ^ 2 + ℓ ^ 2) - 0)) :=
        ((hnorm_shift_sq.add hnorm_sq).const_mul 2).sub hdiff_sq
      simpa [hrewrite] using haux
    have hsum_sq_lower : 2 * (ℓ ^ 2 + ℓ ^ 2) ≤ ‖x (n + m) + x n‖ ^ 2 := by
      -- Antitonicity of the sum norms keeps every term above its limiting square.
      exact
        le_of_tendsto_of_tendsto hsum_sq_tendsto tendsto_const_nhds <|
          Filter.eventually_atTop.2 ⟨n, fun k hk ↦ hsum_sq_antitone hk⟩
    have hnorm_shift_le : ‖x (n + m)‖ ≤ ‖x n‖ := hnorm_antitone (Nat.le_add_right n m)
    -- The parallelogram identity converts the lower bound on the sum norm into the Cauchy bound.
    nlinarith [parallelogram_law_with_norm (𝕜 := ℝ) (x (n + m)) (x n), hsum_sq_lower,
      hnorm_shift_le,
      norm_nonneg (x (n + m)), norm_nonneg (x n)]
  have hinside_nonneg : ∀ N : ℕ, 0 ≤ 4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2 := by
    intro N
    nlinarith [hℓ_le_norm N, hℓ_nonneg, norm_nonneg (x N)]
  have hbound_tendsto :
      Tendsto (fun N ↦ Real.sqrt (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    have hinside :
        Tendsto (fun N ↦ 4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      have hsq :
          Tendsto (fun N ↦ ‖x N‖ ^ 2) atTop (𝓝 (ℓ ^ 2)) := by
        simpa using hℓ_tendsto.pow 2
      have haux :
          Tendsto (fun N ↦ 4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2) atTop (𝓝 (4 * ℓ ^ 2 - 4 * ℓ ^ 2)) :=
        (hsq.const_mul 4).sub tendsto_const_nhds
      simpa using haux
    -- The explicit square-root tail bound tends to `0`.
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hinside
  have hcauchy : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ Real.sqrt (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2)) ?_
      hbound_tendsto
    intro n m N hNn hNm
    by_cases hnm : n ≤ m
    · rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
      have hsq_bound :
          ‖x (n + k) - x n‖ ^ 2 ≤ 4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2 := by
        have hnorm_n_le : ‖x n‖ ≤ ‖x N‖ := hnorm_antitone hNn
        nlinarith [hdiff_sq_le n k, hnorm_n_le, norm_nonneg (x n), norm_nonneg (x N)]
      rw [dist_eq_norm]
      have hdist_sq :
          ‖x n - x (n + k)‖ ^ 2 ≤ (Real.sqrt (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2)) ^ 2 := by
        simpa [Real.sq_sqrt (hinside_nonneg N), norm_sub_rev] using hsq_bound
      exact le_of_sq_le_sq hdist_sq (Real.sqrt_nonneg (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2))
    · have hmn : m ≤ n := le_of_not_ge hnm
      rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
      have hsq_bound :
          ‖x (m + k) - x m‖ ^ 2 ≤ 4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2 := by
        have hnorm_m_le : ‖x m‖ ≤ ‖x N‖ := hnorm_antitone hNm
        nlinarith [hdiff_sq_le m k, hnorm_m_le, norm_nonneg (x m), norm_nonneg (x N)]
      rw [dist_eq_norm, norm_sub_rev]
      have hdist_sq :
          ‖x m - x (m + k)‖ ^ 2 ≤ (Real.sqrt (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2)) ^ 2 := by
        simpa [Real.sq_sqrt (hinside_nonneg N), norm_sub_rev] using hsq_bound
      exact le_of_sq_le_sq hdist_sq (Real.sqrt_nonneg (4 * ‖x N‖ ^ 2 - 4 * ℓ ^ 2))
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨z, hz⟩
  have hzD : z ∈ D := by
    -- Closedness of `D` returns the strong limit of the Picard orbit to the domain.
    exact hD_closed.mem_of_tendsto hz <|
      Filter.Eventually.of_forall fun n ↦ ((T^[n]) x₀).2
  let zD : D := ⟨z, hzD⟩
  have hweak_z :
      Tendsto (fun n ↦ toWeakSpace ℝ H ((T^[n]) x₀ : H)) atTop
        (𝓝 (toWeakSpace ℝ H z)) := by
    -- Strong convergence upgrades automatically to weak convergence.
    simpa [x, toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto z).comp hz
  have hz_fixed_val : T zD = (z : H) := by
    -- Demiclosedness identifies the strong limit as an actual fixed point of `T`.
    simpa [zD] using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        hD_closed hD_convex hT hweak_z hres
  have hz_fixed : zD ∈ Function.fixedPoints T := by
    rw [Function.mem_fixedPoints_iff]
    exact Subtype.ext hz_fixed_val
  exact ⟨zD, hz_fixed, by simpa [x] using hz⟩

end
