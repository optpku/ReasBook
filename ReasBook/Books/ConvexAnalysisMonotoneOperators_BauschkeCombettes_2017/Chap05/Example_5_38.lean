/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Corollary_5_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- The Cesaro averages of the Picard iterates of a self-map of `D`. -/
noncomputable def cesaroIterates (T : D → D) (x₀ : D) : ℕ → H :=
  fun n ↦ (1 / (n + 1 : ℝ)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k]) x₀ : H))

-- Proof sketch: each iterate `((T^[k]) x₀ : H)` lies in `D`; the coefficients `1 / (n + 1)` are
-- nonnegative and sum to `1`, so convexity of `D` keeps their finite average inside `D`.
/-- Convexity keeps the Cesaro averages of the Picard iterates inside the domain. -/
theorem cesaroIterates_mem (hD_convex : Convex ℝ D) (T : D → D) (x₀ : D) (n : ℕ) :
    cesaroIterates T x₀ n ∈ D := by
  have hweight_nonneg :
      ∀ k ∈ Finset.range (n + 1), 0 ≤ (1 / (n + 1 : ℝ)) := by
    intro k hk
    positivity
  have hweight_sum :
      Finset.sum (Finset.range (n + 1)) (fun _ ↦ (1 / (n + 1 : ℝ))) = 1 := by
    have hnp1 : (n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hnp1]
  -- Every Picard iterate already lies in `D`, so convexity keeps their uniform average in `D`.
  simpa [cesaroIterates, Finset.smul_sum] using
    hD_convex.sum_mem hweight_nonneg hweight_sum (fun k hk ↦ ((T^[k]) x₀).2)

end

section

variable {X : Type*} [AddCommGroup X]

/-- Helper for Example 5.38: finite sums of first-order differences telescope to the endpoint
difference. -/
private lemma sum_range_sub_shift (u : ℕ → X) (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ u i - u (i + 1)) = u 0 - u N := by
  induction N with
  | zero =>
      simp
  | succ N hN =>
      -- Extend the telescope by one last increment and combine endpoint terms.
      rw [Finset.sum_range_succ, hN]
      abel_nf

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H}

/-- Helper for Example 5.38: a subtype map is quasinonexpansive when it decreases distances to
its fixed points. -/
private def IsQuasinonexpansiveOn (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) → dist (T x) y ≤ dist (x : H) y

/-- Helper for Example 5.38: the Picard orbit of a quasinonexpansive map is Fejér monotone with
respect to the ambient realization of its fixed-point set. -/
private theorem quasinonexpansive_iterates_fejer_monotone
    (T : D → D) (hT : IsQuasinonexpansiveOn (fun x : D ↦ (T x : H))) (x₀ : D) :
    FejerMonotone (Subtype.val '' Function.fixedPoints T) (fun n ↦ ((T^[n]) x₀ : H)) := by
  intro z hz n
  rcases hz with ⟨y, hyfix, rfl⟩
  -- Convert the subtype fixed-point equality into the ambient equality used by the hypothesis.
  have hy : (T y : H) = y := by
    exact congrArg Subtype.val (Function.mem_fixedPoints_iff.mp hyfix)
  -- Apply quasinonexpansiveness to the nth Picard iterate and rewrite the successor iterate.
  simpa [dist_eq_norm, Function.iterate_succ_apply', Nat.succ_eq_add_one] using
    hT ((T^[n]) x₀) y hy

/-- Helper for Example 5.38: the shifted Cesaro average differs from the original average by a
single endpoint contribution. -/
private lemma shifted_cesaroIterates_sub_eq_endpoint_difference
    {T : D → D} (x₀ : D) (n : ℕ) :
    ((1 / (n + 1 : ℝ)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H))) -
        cesaroIterates T x₀ n =
      (1 / (n + 1 : ℝ)) • (((T^[n + 1]) x₀ : H) - (x₀ : H)) := by
  let u : ℕ → H := fun k ↦ ((T^[k]) x₀ : H)
  have hsum :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ u (k + 1)) -
          Finset.sum (Finset.range (n + 1)) u =
        u (n + 1) - u 0 := by
    -- Rewrite the two finite sums as one sum of differences and telescope the resulting chain.
    calc
      Finset.sum (Finset.range (n + 1)) (fun k ↦ u (k + 1)) -
          Finset.sum (Finset.range (n + 1)) u
          = Finset.sum (Finset.range (n + 1)) (fun k ↦ u (k + 1) - u k) := by
              rw [← Finset.sum_sub_distrib]
      _ = Finset.sum (Finset.range (n + 1)) (fun k ↦ -(u k - u (k + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            abel_nf
      _ = -Finset.sum (Finset.range (n + 1)) (fun k ↦ u k - u (k + 1)) := by
            rw [Finset.sum_neg_distrib]
      _ = -(u 0 - u (n + 1)) := by
            rw [sum_range_sub_shift]
      _ = u (n + 1) - u 0 := by
            abel_nf
  -- Factor out the common Cesaro weight and substitute the telescoped endpoint difference.
  calc
    ((1 / (n + 1 : ℝ)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H))) -
        cesaroIterates T x₀ n
        =
      (1 / (n + 1 : ℝ)) •
        (Finset.sum (Finset.range (n + 1)) (fun k ↦ u (k + 1)) -
          Finset.sum (Finset.range (n + 1)) u) := by
            rw [cesaroIterates, ← smul_sub]
    _ = (1 / (n + 1 : ℝ)) • (u (n + 1) - u 0) := by
          rw [hsum]
    _ = (1 / (n + 1 : ℝ)) • (((T^[n + 1]) x₀ : H) - (x₀ : H)) := by
          simp [u]

/-- Helper for Example 5.38: the shifted squared-distance matrix telescope leaves only the
boundary-strip terms. -/
private lemma pairwise_shifted_sqdist_gap_eq_endpoint_sum
    (u : ℕ → H) (n : ℕ) :
    (1 / 2 : ℝ) *
        Finset.sum (Finset.range (n + 1)) (fun k ↦
          Finset.sum (Finset.range (n + 1)) (fun l ↦
            ‖u k - u l‖ ^ 2 - ‖u (k + 1) - u (l + 1)‖ ^ 2)) =
      Finset.sum (Finset.range n) (fun k ↦
        ‖u (k + 1) - u 0‖ ^ 2 - ‖u (k + 1) - u (n + 1)‖ ^ 2) := by
  let a : ℕ → ℕ → ℝ := fun k l ↦ ‖u k - u l‖ ^ 2
  have hsymm : ∀ k l, a k l = a l k := by
    intro k l
    simp [a, norm_sub_rev]
  have hdiag : ∀ k, a k k = 0 := by
    intro k
    simp [a]
  have hmain :
      Finset.sum (Finset.range (n + 1)) (fun k ↦
          Finset.sum (Finset.range (n + 1)) (fun l ↦ a k l - a (k + 1) (l + 1))) =
        (2 : ℝ) *
          Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0 - a (k + 1) (n + 1)) := by
    let v : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range n) (fun l ↦ a k (l + 1))
    have hinner :
        ∀ k,
          Finset.sum (Finset.range (n + 1)) (fun l ↦ a k l - a (k + 1) (l + 1)) =
            a k 0 + (v k - v (k + 1)) - a (k + 1) (n + 1) := by
      intro k
      -- Split the inner row sum into the left boundary, the common interior block, and the right
      -- boundary of the shifted square.
      calc
        Finset.sum (Finset.range (n + 1)) (fun l ↦ a k l - a (k + 1) (l + 1))
            = Finset.sum (Finset.range (n + 1)) (fun l ↦ a k l) -
                Finset.sum (Finset.range (n + 1)) (fun l ↦ a (k + 1) (l + 1)) := by
                  rw [← Finset.sum_sub_distrib]
        _ = (Finset.sum (Finset.range n) (fun l ↦ a k (l + 1)) + a k 0) -
              (Finset.sum (Finset.range n) (fun l ↦ a (k + 1) (l + 1)) + a (k + 1) (n + 1)) := by
                rw [Finset.sum_range_succ', Finset.sum_range_succ]
        _ = a k 0 + (v k - v (k + 1)) - a (k + 1) (n + 1) := by
              simp [v]
              ring
    calc
      Finset.sum (Finset.range (n + 1)) (fun k ↦
          Finset.sum (Finset.range (n + 1)) (fun l ↦ a k l - a (k + 1) (l + 1)))
          = Finset.sum (Finset.range (n + 1)) (fun k ↦ a k 0 + (v k - v (k + 1)) - a (k + 1) (n + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [hinner k]
      _ = Finset.sum (Finset.range (n + 1)) (fun k ↦ a k 0) +
            Finset.sum (Finset.range (n + 1)) (fun k ↦ (v k - v (k + 1))) -
            Finset.sum (Finset.range (n + 1)) (fun k ↦ a (k + 1) (n + 1)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0) + a 0 0) +
            (v 0 - v (n + 1)) -
            (Finset.sum (Finset.range n) (fun k ↦ a (k + 1) (n + 1)) + a (n + 1) (n + 1)) := by
              rw [Finset.sum_range_succ', sum_range_sub_shift, Finset.sum_range_succ]
      _ = (Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0) + a 0 0) +
            ((Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0)) -
              (Finset.sum (Finset.range n) (fun k ↦ a (k + 1) (n + 1)))) -
            (Finset.sum (Finset.range n) (fun k ↦ a (k + 1) (n + 1)) + a (n + 1) (n + 1)) := by
              have hv0 :
                  v 0 = Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0) := by
                simp [v]
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [hsymm 0 (k + 1)]
              have hvn :
                  v (n + 1) = Finset.sum (Finset.range n) (fun k ↦ a (k + 1) (n + 1)) := by
                simp [v]
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [hsymm (n + 1) (k + 1)]
              rw [hv0, hvn]
      _ = (2 : ℝ) * Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0 - a (k + 1) (n + 1)) := by
            simp [hdiag]
            ring
  -- The distance matrix is symmetric, so the surviving boundary strips appear twice.
  calc
    (1 / 2 : ℝ) *
        Finset.sum (Finset.range (n + 1)) (fun k ↦
          Finset.sum (Finset.range (n + 1)) (fun l ↦
            ‖u k - u l‖ ^ 2 - ‖u (k + 1) - u (l + 1)‖ ^ 2))
        = (1 / 2 : ℝ) *
            ((2 : ℝ) * Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0 - a (k + 1) (n + 1))) := by
              rw [hmain]
    _ = Finset.sum (Finset.range n) (fun k ↦ a (k + 1) 0 - a (k + 1) (n + 1)) := by ring
    _ = Finset.sum (Finset.range n) (fun k ↦
          ‖u (k + 1) - u 0‖ ^ 2 - ‖u (k + 1) - u (n + 1)‖ ^ 2) := by
            simp [a]

/-- Helper for Example 5.38: a scalar factor can be pulled out of the shifted double sum with
uniform weights. -/
private lemma double_sum_const_mul (c : ℝ) (g : ℕ → ℕ → ℝ) (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun k ↦
      Finset.sum (Finset.range (n + 1)) (fun l ↦ c * g k l)) =
      c * Finset.sum (Finset.range (n + 1)) (fun k ↦
        Finset.sum (Finset.range (n + 1)) (fun l ↦ g k l)) := by
  -- Pull the common scalar out of the inner sums and then out of the outer sum.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mul_sum]

/-- Helper for Example 5.38: Proposition 4.8 yields the Baillon bound for the nonlinearity defect
between `T x_n` and the shifted Cesaro average. -/
private theorem sq_norm_T_cesaroIterates_sub_shifted_average_le
    (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T) (x₀ : D) (n : ℕ) :
    ‖(T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) -
        (1 / (n + 1 : ℝ)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H))‖ ^ 2 ≤
      (1 / (n + 1 : ℝ)) ^ 2 *
        Finset.sum (Finset.range n)
          (fun k ↦ ‖((T^[k + 1]) x₀ : H) - (x₀ : H)‖ ^ 2 -
            ‖((T^[k + 1]) x₀ : H) - ((T^[n + 1]) x₀ : H)‖ ^ 2) := by
  -- Route correction: Proposition 4.8 is formulated for ambient maps `H → H`, so first extend the
  -- subtype self-map `T : D → D` to an ambient map that agrees with `T` on `D`.
  let S : H → H :=
    Function.extend Subtype.val (fun z : D ↦ (T z : H)) (fun _ ↦ (x₀ : H))
  let x : ℕ → H := fun k ↦ ((T^[k]) x₀ : H)
  let α : ℕ → ℝ := fun _ ↦ 1 / (n + 1 : ℝ)
  have hS_lipschitz : LipschitzOnWith 1 S D := by
    intro x₁ hx₁ x₂ hx₂
    have hx₁_ext : S x₁ = (T ⟨x₁, hx₁⟩ : H) := by
      simpa [S] using
        (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ (x₀ : H))
          ⟨x₁, hx₁⟩)
    have hx₂_ext : S x₂ = (T ⟨x₂, hx₂⟩ : H) := by
      simpa [S] using
        (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ (x₀ : H))
          ⟨x₂, hx₂⟩)
    -- On points of `D`, the ambient extension coincides with the original nonexpansive map.
    rw [hx₁_ext, hx₂_ext]
    simpa [Subtype.edist_eq] using hT.edist_le_mul ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  have hy :
      cesaroIterates T x₀ n =
        Finset.sum (Finset.range (n + 1)) (fun k ↦ α k • x k) := by
    -- The Cesaro average is exactly the weighted barycenter with uniform coefficients.
    simp [cesaroIterates, α, x, Finset.smul_sum]
  have hα_nonneg : ∀ k ∈ Finset.range (n + 1), 0 ≤ α k := by
    intro k hk
    positivity
  have hα_sum : Finset.sum (Finset.range (n + 1)) (fun k ↦ α k) = 1 := by
    have hnp1 : (n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    rw [show (fun k ↦ α k) = fun _ ↦ (1 / (n + 1 : ℝ)) by
      funext k
      simp [α]]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hnp1]
  have hx_mem : ∀ k ∈ Finset.range (n + 1), x k ∈ D := by
    intro k hk
    exact ((T^[k]) x₀).2
  have hS_cesaro :
      S (cesaroIterates T x₀ n) =
        (T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) := by
    -- The barycenter lies in `D`, so the ambient extension reduces back to `T`.
    simpa [S] using
      (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ (x₀ : H))
        ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩)
  have hS_iter : ∀ k, S (x k) = x (k + 1) := by
    intro k
    -- Each Picard iterate stays in `D`, so one more application of the extension gives the next
    -- iterate in the orbit.
    calc
      S (x k) = (T ((T^[k]) x₀) : H) := by
        simpa [S, x] using
          (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ (x₀ : H))
            ((T^[k]) x₀))
      _ = x (k + 1) := by
        simp [x, Function.iterate_succ_apply']
  have hraw :=
    zarantonello_weighted_nonexpansive_inequality
      (s := Finset.range (n + 1)) (D := D) hD_convex S x α (cesaroIterates T x₀ n)
      hy hα_nonneg hα_sum hx_mem hS_lipschitz
  have hsum_shift :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ α k • S (x k)) =
        (1 / (n + 1 : ℝ)) •
          Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H)) := by
    -- Rewrite each shifted image term using the ambient extension, then factor out the constant
    -- weight.
    calc
      Finset.sum (Finset.range (n + 1)) (fun k ↦ α k • S (x k))
          = Finset.sum (Finset.range (n + 1))
              (fun k ↦ (1 / (n + 1 : ℝ)) • ((T^[k + 1]) x₀ : H)) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simpa [α] using congrArg (fun y ↦ α k • y) (hS_iter k)
      _ = (1 / (n + 1 : ℝ)) •
            Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H)) := by
              rw [Finset.smul_sum]
  let rhs : ℝ :=
    (1 / 2 : ℝ) * Finset.sum (Finset.range (n + 1)) (fun k ↦
      Finset.sum (Finset.range (n + 1)) (fun l ↦
        α k * α l * (‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2)))
  have hbound :
      ‖(T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) -
          (1 / (n + 1 : ℝ)) •
            Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H))‖ ^ 2
        ≤ rhs := by
    convert hraw using 1
    · rw [hS_cesaro, hsum_shift]
    · dsimp [rhs]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro k hk
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [hS_iter k, hS_iter l]
  -- Pull the constant weight square out of the double sum, then collapse the shifted matrix gap to
  -- the boundary-strip expression from the source proof.
  calc
    ‖(T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) -
        (1 / (n + 1 : ℝ)) •
          Finset.sum (Finset.range (n + 1)) (fun k ↦ ((T^[k + 1]) x₀ : H))‖ ^ 2
        ≤
      rhs := hbound
    _ =
      (1 / (n + 1 : ℝ)) ^ 2 *
        ((1 / 2 : ℝ) *
          Finset.sum (Finset.range (n + 1)) (fun k ↦
            Finset.sum (Finset.range (n + 1)) (fun l ↦
              ‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2))) := by
            dsimp [rhs]
            calc
              (1 / 2 : ℝ) *
                  Finset.sum (Finset.range (n + 1)) (fun k ↦
                    Finset.sum (Finset.range (n + 1)) (fun l ↦
                      α k * α l *
                        (‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2)))
                  =
                (1 / 2 : ℝ) *
                  Finset.sum (Finset.range (n + 1)) (fun k ↦
                    Finset.sum (Finset.range (n + 1)) (fun l ↦
                      ((1 / (n + 1 : ℝ)) ^ 2) *
                        (‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2))) := by
                          congr 1
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          refine Finset.sum_congr rfl ?_
                          intro l hl
                          have hαsq : α k * α l = (1 / (n + 1 : ℝ)) ^ 2 := by
                            simp [α, pow_two]
                          rw [hαsq]
              _ =
                (1 / 2 : ℝ) *
                  (((1 / (n + 1 : ℝ)) ^ 2) *
                    Finset.sum (Finset.range (n + 1)) (fun k ↦
                      Finset.sum (Finset.range (n + 1)) (fun l ↦
                        ‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2))) := by
                          rw [double_sum_const_mul]
              _ =
                (1 / (n + 1 : ℝ)) ^ 2 *
                  ((1 / 2 : ℝ) *
                    Finset.sum (Finset.range (n + 1)) (fun k ↦
                      Finset.sum (Finset.range (n + 1)) (fun l ↦
                        ‖x k - x l‖ ^ 2 - ‖x (k + 1) - x (l + 1)‖ ^ 2))) := by
                          ring
    _ =
      (1 / (n + 1 : ℝ)) ^ 2 *
        Finset.sum (Finset.range n) (fun k ↦
          ‖x (k + 1) - x 0‖ ^ 2 - ‖x (k + 1) - x (n + 1)‖ ^ 2) := by
            congr 1
            exact pairwise_shifted_sqdist_gap_eq_endpoint_sum x n
    _ =
      (1 / (n + 1 : ℝ)) ^ 2 *
        Finset.sum (Finset.range n) (fun k ↦
          ‖((T^[k + 1]) x₀ : H) - (x₀ : H)‖ ^ 2 -
            ‖((T^[k + 1]) x₀ : H) - ((T^[n + 1]) x₀ : H)‖ ^ 2) := by
              simp [x]

/-- Helper for Example 5.38: the Cesaro residual `T x_n - x_n` tends strongly to `0`. -/
private theorem T_cesaroIterates_sub_cesaroIterates_tendsto_zero
    (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hFix : (Function.fixedPoints T).Nonempty) (x₀ : D) :
    Tendsto
      (fun n ↦
        (T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) -
          cesaroIterates T x₀ n)
      atTop (𝓝 (0 : H)) := by
  let x : ℕ → H := fun n ↦ ((T^[n]) x₀ : H)
  let z : ℕ → H := fun n ↦
    (1 / (n + 1 : ℝ)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ x (k + 1))
  let C : Set H := Subtype.val '' Function.fixedPoints T
  let defect : ℕ → H := fun n ↦
    (T ⟨cesaroIterates T x₀ n, cesaroIterates_mem hD_convex T x₀ n⟩ : H) - z n
  have hquasi : IsQuasinonexpansiveOn (fun y : D ↦ (T y : H)) := by
    intro y₁ y₂ hy₂
    -- A nonexpansive self-map decreases distances to each of its fixed points.
    have hy : ‖(T y₁ : H) - (T y₂ : H)‖ ≤ ‖(y₁ : H) - y₂‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT.dist_le_mul y₁ y₂
    have hy' : ‖(T y₁ : H) - y₂‖ ≤ ‖(y₁ : H) - y₂‖ := by
      simpa [hy₂] using hy
    simpa [dist_eq_norm] using hy'
  have hfejer : FejerMonotone C x := by
    -- Example 5.3 gives the Fejer monotonicity of the Picard orbit.
    simpa [C, x] using quasinonexpansive_iterates_fejer_monotone T hquasi x₀
  have hC_nonempty : C.Nonempty := by
    rcases hFix with ⟨p, hp⟩
    exact ⟨p, ⟨p, hp, rfl⟩⟩
  let M : ℝ := 2 * Metric.infDist (x₀ : H) C
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    nlinarith [Metric.infDist_nonneg (x := (x₀ : H)) (s := C)]
  have hendpoint_bound : ∀ m, ‖x m - (x₀ : H)‖ ≤ M := by
    intro m
    -- Proposition 5.4(iv) bounds each orbit endpoint by twice the initial distance to `Fix T`.
    simpa [x, C, M, dist_eq_norm, Nat.zero_add] using
      hfejer.dist_le_two_mul_infDist hC_nonempty m 0
  have hendpoint_sq_bound : ∀ m, ‖x m - (x₀ : H)‖ ^ 2 ≤ M ^ 2 := by
    intro m
    exact (sq_le_sq₀ (norm_nonneg _) hM_nonneg).2 (hendpoint_bound m)
  have hinv_tendsto : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    -- The reciprocal tail `1 / (n + 1)` tends to `0`.
    simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hdefect_sq_le : ∀ n, ‖defect n‖ ^ 2 ≤ M ^ 2 * (1 / (n + 1 : ℝ)) := by
    intro n
    have hsq :=
      sq_norm_T_cesaroIterates_sub_shifted_average_le hD_convex hT x₀ n
    have hdrop :
        Finset.sum (Finset.range n) (fun k ↦
            ‖x (k + 1) - (x₀ : H)‖ ^ 2 - ‖x (k + 1) - x (n + 1)‖ ^ 2) ≤
          Finset.sum (Finset.range n) (fun k ↦ ‖x (k + 1) - (x₀ : H)‖ ^ 2) := by
      -- Drop the nonnegative second term in each summand.
      refine Finset.sum_le_sum ?_
      intro k hk
      have hnonneg : 0 ≤ ‖x (k + 1) - x (n + 1)‖ ^ 2 := sq_nonneg _
      linarith
    have hsum_le :
        Finset.sum (Finset.range n) (fun k ↦ ‖x (k + 1) - (x₀ : H)‖ ^ 2) ≤
          (n + 1 : ℝ) * M ^ 2 := by
      calc
        Finset.sum (Finset.range n) (fun k ↦ ‖x (k + 1) - (x₀ : H)‖ ^ 2)
            ≤ Finset.sum (Finset.range n) (fun _ ↦ M ^ 2) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                exact hendpoint_sq_bound (k + 1)
        _ = (n : ℝ) * M ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (n + 1 : ℝ) * M ^ 2 := by
              have hcast : (n : ℝ) ≤ n + 1 := by
                exact_mod_cast (Nat.le_succ n)
              gcongr
    have hcoeff_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) ^ 2 := sq_nonneg _
    calc
      ‖defect n‖ ^ 2
          ≤ (1 / (n + 1 : ℝ)) ^ 2 *
              Finset.sum (Finset.range n) (fun k ↦
                ‖x (k + 1) - (x₀ : H)‖ ^ 2 - ‖x (k + 1) - x (n + 1)‖ ^ 2) := by
                simpa [defect, z, x] using hsq
      _ ≤ (1 / (n + 1 : ℝ)) ^ 2 *
            Finset.sum (Finset.range n) (fun k ↦ ‖x (k + 1) - (x₀ : H)‖ ^ 2) := by
              gcongr
      _ ≤ (1 / (n + 1 : ℝ)) ^ 2 * ((n + 1 : ℝ) * M ^ 2) := by
            gcongr
      _ = M ^ 2 * (1 / (n + 1 : ℝ)) := by
            have hnp1 : (n + 1 : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero n)
            field_simp [pow_two, hnp1]
  have hdefect_sq_tendsto :
      Tendsto (fun n ↦ ‖defect n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hupper :
        Tendsto (fun n : ℕ ↦ M ^ 2 * (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      simpa [mul_comm] using hinv_tendsto.mul_const (M ^ 2)
    -- The squared Baillon defect is squeezed by the reciprocal rate.
    exact squeeze_zero (fun n ↦ sq_nonneg ‖defect n‖) hdefect_sq_le hupper
  have hdefect_norm_tendsto :
      Tendsto (fun n ↦ ‖defect n‖) atTop (𝓝 (0 : ℝ)) := by
    -- Passing through `Real.sqrt` converts the squared-norm convergence into norm convergence.
    have hsqrt :
        Tendsto (fun n ↦ Real.sqrt (‖defect n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) := by
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hdefect_sq_tendsto
    simpa [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
  have hdefect_tendsto : Tendsto defect atTop (𝓝 (0 : H)) := by
    -- Vanishing norms are equivalent to strong convergence to zero.
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hdefect_norm_tendsto
  have hz_sub_eq :
      ∀ n, z n - cesaroIterates T x₀ n =
        (1 / (n + 1 : ℝ)) • (x (n + 1) - (x₀ : H)) := by
    intro n
    -- The shifted and unshifted Cesaro averages differ only by the two orbit endpoints.
    simpa [z, x] using shifted_cesaroIterates_sub_eq_endpoint_difference (T := T) x₀ n
  have hz_norm_le : ∀ n, ‖z n - cesaroIterates T x₀ n‖ ≤ M * (1 / (n + 1 : ℝ)) := by
    intro n
    rw [hz_sub_eq n, norm_smul, Real.norm_of_nonneg (by positivity)]
    -- The endpoint estimate from Fejer monotonicity controls the whole shifted-average error.
    have hcoeff_nonneg : 0 ≤ 1 / (n + 1 : ℝ) := by
      positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hendpoint_bound (n + 1)) hcoeff_nonneg
  have hz_norm_tendsto :
      Tendsto (fun n ↦ ‖z n - cesaroIterates T x₀ n‖) atTop (𝓝 (0 : ℝ)) := by
    have hupper :
        Tendsto (fun n : ℕ ↦ M * (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      simpa [mul_comm] using hinv_tendsto.mul_const M
    -- The shifted-average difference has the explicit reciprocal decay from (5.57).
    exact squeeze_zero (fun n ↦ norm_nonneg _) hz_norm_le hupper
  have hz_tendsto :
      Tendsto (fun n ↦ z n - cesaroIterates T x₀ n) atTop (𝓝 (0 : H)) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hz_norm_tendsto
  have hsum :
      Tendsto (fun n ↦ defect n + (z n - cesaroIterates T x₀ n)) atTop (𝓝 (0 : H)) := by
    simpa using hdefect_tendsto.add hz_tendsto
  -- Split `T x_n - x_n` through the shifted Cesaro average and add the two vanishing pieces.
  convert hsum using 1 with n
  dsimp [defect]
  abel_nf

/-- Helper for Example 5.38: every weak sequential cluster point of the Cesaro averages belongs to
the ambient image of the fixed-point set. -/
private theorem weak_cluster_point_mem_fixedPoints_image_of_cesaroIterates
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hFix : (Function.fixedPoints T).Nonempty) (x₀ : D) {z : H}
    (hz :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (cesaroIterates T x₀ n))
        (toWeakSpace ℝ H z)) :
    z ∈ Subtype.val '' Function.fixedPoints T := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
  have hzD : z ∈ D := by
    -- Closed convexity keeps the weak limit of a Cesaro subsequence inside `D`.
    have hD_weakClosed : IsClosed ((toWeakSpace ℝ H) '' D) :=
      (isClosed_iff_weak_image_isClosed_of_convex hD_convex).1 hD_closed
    have hzWeak :
        toWeakSpace ℝ H z ∈ closure ((toWeakSpace ℝ H) '' D) := by
      exact mem_closure_of_tendsto hφz <|
        Filter.Eventually.of_forall fun n ↦
          ⟨cesaroIterates T x₀ (φ n), cesaroIterates_mem hD_convex T x₀ (φ n), rfl⟩
    rw [hD_weakClosed.closure_eq] at hzWeak
    rcases hzWeak with ⟨y, hyD, hyz⟩
    exact (toWeakSpace ℝ H).injective hyz ▸ hyD
  let zD : D := ⟨z, hzD⟩
  have hres_sub :
      Tendsto
        (fun n ↦
          cesaroIterates T x₀ (φ n) -
            (T ⟨cesaroIterates T x₀ (φ n), cesaroIterates_mem hD_convex T x₀ (φ n)⟩ : H))
        atTop (𝓝 (0 : H)) := by
    -- Residual decay persists after passage to the convergent subsequence.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((T_cesaroIterates_sub_cesaroIterates_tendsto_zero hD_convex hT hFix x₀).comp
        hφ.tendsto_atTop).neg
  have hz_fixed : T zD = (z : H) := by
    have hφz' :
        Tendsto
          (fun n ↦
            toWeakSpace ℝ H
              ((⟨cesaroIterates T x₀ (φ n), cesaroIterates_mem hD_convex T x₀ (φ n)⟩ : D) : H))
          atTop (𝓝 (toWeakSpace ℝ H (zD : H))) := by
      -- Package the subsequence as a sequence in `D` to match Corollary 4.28.
      simpa [zD] using hφz
    -- Demiclosedness turns the weak limit of approximate fixed points into an actual fixed point.
    simpa [zD] using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        (xₙ := fun n ↦
          ⟨cesaroIterates T x₀ (φ n), cesaroIterates_mem hD_convex T x₀ (φ n)⟩)
        (x := zD) hD_closed hD_convex hT hφz' hres_sub
  refine ⟨zD, ?_, rfl⟩
  rw [Function.mem_fixedPoints_iff]
  exact Subtype.ext (by simpa [zD] using hz_fixed)

-- Proof sketch: the Picard orbit `n ↦ ((T^[n]) x₀ : H)` is Fejér monotone with respect to
-- `Function.fixedPoints T`. The uniform weights defining `cesaroIterates T x₀` satisfy the
-- hypotheses of Corollary 5.37, and the Baillon asymptotic-regularity argument shows that every
-- weak sequential cluster point of these averages is a fixed point via Corollary 4.28. The
-- nonlinear ergodic theorem then yields weak convergence to some point of `Function.fixedPoints T`.
/-- Example 5.38 (Baillon): if `D` is a closed convex subset of a real Hilbert space, `T : D → D`
is nonexpansive, and `Fix T` is nonempty, then the Cesaro averages of the Picard iterates of `x₀`
converge weakly to a fixed point of `T`. -/
theorem tendsto_weakly_cesaroIterates_to_fixedPoint_of_nonexpansive
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hFix : (Function.fixedPoints T).Nonempty) (x₀ : D) :
    ∃ z ∈ Function.fixedPoints T,
      Tendsto (fun n ↦ toWeakSpace ℝ H (cesaroIterates T x₀ n)) atTop
        (𝓝 (toWeakSpace ℝ H (z : H))) := by
  let y : ℕ → H := fun n ↦ ((T^[n]) x₀ : H)
  let α : ℕ → ℕ → ℝ := fun n _ ↦ 1 / (n + 1 : ℝ)
  have hquasi : IsQuasinonexpansiveOn (fun x : D ↦ (T x : H)) := by
    intro x y hy
    -- A `1`-Lipschitz self-map is quasinonexpansive against each fixed point.
    have hxy : ‖(T x : H) - (T y : H)‖ ≤ ‖(x : H) - y‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT.dist_le_mul x y
    have hxy' : ‖(T x : H) - y‖ ≤ ‖(x : H) - y‖ := by
      simpa [hy] using hxy
    simpa [dist_eq_norm] using hxy'
  have hfejer :
      FejerMonotone (Subtype.val '' Function.fixedPoints T) y := by
    -- Example 5.3 turns the Picard orbit into a Fejer-monotone sequence.
    simpa [y] using quasinonexpansive_iterates_fejer_monotone T hquasi x₀
  have hqfejer : QuasiFejerMonotone (Subtype.val '' Function.fixedPoints T) y :=
    hfejer.quasiFejerMonotone
  have hFix_image : (Subtype.val '' Function.fixedPoints T).Nonempty := by
    rcases hFix with ⟨z, hz⟩
    exact ⟨z, ⟨z, hz, rfl⟩⟩
  have hα_nonneg : ∀ n k, k ≤ n → 0 ≤ α n k := by
    intro n k hkn
    positivity
  have hα_sum : ∀ n, Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k) = 1 := by
    intro n
    have hnp1 : (n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    rw [show (fun k ↦ α n k) = fun _ ↦ (1 / (n + 1 : ℝ)) by
      funext k
      simp [α]]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hnp1]
  have hα_tendsto : ∀ k, Tendsto (fun n ↦ α n k) atTop (𝓝 0) := by
    intro k
    have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    -- Each fixed coefficient column is the reciprocal tail `1 / (n + 1)`.
    simpa [α, Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n ↦
              toWeakSpace ℝ H
                (Finset.sum (Finset.range (n + 1)) (fun k ↦ α n k • y k)))
            (toWeakSpace ℝ H z) →
          z ∈ Subtype.val '' Function.fixedPoints T := by
    intro z hz
    -- The remaining cluster-point hypothesis is exactly the Baillon residual lemma proved above.
    have hz' :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (cesaroIterates T x₀ n))
          (toWeakSpace ℝ H z) := by
      simpa [α, y, cesaroIterates, Finset.smul_sum] using hz
    exact
      weak_cluster_point_mem_fixedPoints_image_of_cesaroIterates
        hD_closed hD_convex hT hFix x₀ hz'
  -- Apply Corollary 5.37 to the uniform Cesaro weights on the Picard orbit.
  rcases
      tendsto_weakly_of_weighted_averages_of_quasiFejerMonotone_of_weakSequentialClusterPts_mem
        (C := Subtype.val '' Function.fixedPoints T) (y := y) (α := α)
        hFix_image hqfejer hα_nonneg hα_sum hα_tendsto hcluster with
    ⟨z, hz, hweak⟩
  rcases hz with ⟨zD, hzD, rfl⟩
  refine ⟨zD, hzD, ?_⟩
  simpa [α, y, cesaroIterates, Finset.smul_sum] using hweak

end
