/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_20
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise
open InnerProductSpace
open Metric

/- Proposition 3.32 is a `source-facing` computation for the owner objective
`fermatWeberObjective`. The `core/canonical` owner is the chapter subdifferential
`subdifferentialAt`, and the Euclidean bridge/view owner is `euclideanSubdifferentialAt`. The
supporting declarations are the finite-sum rule
`subdifferentialAt_finset_sum_eq_sum_subdifferentialAt`, the affine Euclidean-norm formula
`euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise`, and the constant-scaling rule
`subdifferentialAt_const_mul_eq_smul_subdifferentialAt`. The weighted single-site distance term
is therefore only a derived view, not a second public owner abstraction. -/

section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

recall fermatWeberObjective
recall euclideanSubdifferentialAt
recall euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
recall subdifferentialAt_const_mul_eq_smul_subdifferentialAt
recall subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior

/-- Helper for Proposition 3.32: transport the owner-side nonnegative scalar rule from
`subdifferentialAt` to the Euclidean subdifferential bridge. -/
private lemma euclideanSubdifferentialAt_const_mul_eq_smul
    {f : E → ℝ} {x : E}
    (a : ℝ) (ha : 0 ≤ a) (hf : ConvexOn ℝ Set.univ f) :
    euclideanSubdifferentialAt (fun y ↦ a * f y) x = a • euclideanSubdifferentialAt f x := by
  ext z
  rw [mem_euclideanSubdifferentialAt_iff,
    subdifferentialAt_const_mul_eq_smul_subdifferentialAt a ha hf,
    Set.mem_smul_set, Set.mem_smul_set]
  constructor
  · rintro ⟨φ, hφ, hEq⟩
    -- Pull the owner-side witness back through the Riesz identification.
    rcases (toDual ℝ E).surjective φ with ⟨w, rfl⟩
    refine ⟨w, ?_, ?_⟩
    · simpa [mem_euclideanSubdifferentialAt_iff,
        InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hφ
    · apply (toDualMap ℝ E).injective
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hEq
  · rintro ⟨w, hw, rfl⟩
    -- Push the Euclidean witness forward to the owner-side subdifferential.
    refine ⟨toDualMap ℝ E w, ?_, ?_⟩
    · simpa [mem_euclideanSubdifferentialAt_iff] using hw
    · simp

/-- Helper for Proposition 3.32: a linear equivalence sends a finite Minkowski sum of sets to the
corresponding finite sum of the images. -/
private theorem linearEquiv_image_finset_sum
    {κ : Type*}
    (e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) (s : Finset κ)
    (g : κ → Set (Module.Dual ℝ E)) :
    e '' s.sum g = s.sum (fun i ↦ e '' g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext ψ
    simp
  · intro i s hi hs
    simp [Finset.sum_insert, hi, hs, Set.image_add]

/-- Helper for Proposition 3.32: transport the owner finite-sum subdifferential rule to the
Euclidean/vector-side bridge. -/
private lemma euclideanSubdifferentialAt_finset_sum_eq_sum
    (f : Fin m → E → ℝ) (x : E)
    (hconvex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i)) :
    euclideanSubdifferentialAt (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, euclideanSubdifferentialAt (f i) x := by
  classical
  let F : Fin m → E → EReal := fun i y ↦ (f i y : EReal)
  have h_ne_bot : ∀ i : Fin m, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    simp [F]
  have hconvexF : ∀ i : Fin m, is_convex_function (F i) := by
    intro i
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp [F]
    · simpa [F, effective_domain] using hconvex i
  have hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    refine ⟨x, ?_⟩
    simp [F, effective_domain]
  have hsum :
      (fun y ↦ ((∑ i : Fin m, f i y : ℝ) : EReal)) = fun y ↦ ∑ i : Fin m, F i y := by
    funext y
    change Real.toEReal (∑ i : Fin m, f i y) =
      ∑ i : Fin m, Real.toEReal (f i y)
    exact
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun i : Fin m ↦ f i y) Finset.univ
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  have howner :
      subdifferentialAt (fun y ↦ ∑ i : Fin m, f i y) x =
        ∑ i : Fin m, subdifferentialAt (f i) x := by
    have hsub :
        subdifferential (fun y ↦ ∑ i : Fin m, F i y) x =
          ∑ i : Fin m, subdifferential (F i) x :=
      subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
        F x h_ne_bot hconvexF hqual
    have himage :
        e '' subdifferential (fun y ↦ ∑ i : Fin m, F i y) x =
          ∑ i : Fin m, e '' subdifferential (F i) x := by
      rw [hsub]
      simpa [e] using
        linearEquiv_image_finset_sum e Finset.univ (fun i ↦ subdifferential (F i) x)
    have hstrong : ∀ i : Fin m, e '' subdifferential (F i) x = subdifferentialAt (f i) x := by
      intro i
      simpa [subdifferentialAt, F, e] using
        (strongDualSubdifferential_eq_image_subdifferential (F i) x).symm
    calc
      subdifferentialAt (fun y ↦ ∑ i : Fin m, f i y) x
          = strongDualSubdifferential (fun y ↦ ∑ i : Fin m, F i y) x := by
              rw [subdifferentialAt, hsum]
      _ = e '' subdifferential (fun y ↦ ∑ i : Fin m, F i y) x := by
            simpa [e] using
              (strongDualSubdifferential_eq_image_subdifferential
                (fun y ↦ ∑ i : Fin m, F i y) x)
      _ = ∑ i : Fin m, e '' subdifferential (F i) x := himage
      _ = ∑ i : Fin m, subdifferentialAt (f i) x := by
            simp [hstrong]
  ext z
  rw [mem_euclideanSubdifferentialAt_iff, howner, Set.mem_fintype_sum, Set.mem_fintype_sum]
  constructor
  · rintro ⟨φ, hφ, hsum⟩
    -- Choose Euclidean witnesses for each owner-side summand.
    choose w hw using fun i : Fin m ↦ (toDual ℝ E).surjective (φ i)
    have hwi : ∀ i : Fin m, toDualMap ℝ E (w i) = φ i := by
      intro i
      ext y
      have hEval := congrArg (fun ψ : StrongDual ℝ E ↦ ψ y) (hw i)
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hEval
    refine ⟨w, ?_, ?_⟩
    · intro i
      simpa [mem_euclideanSubdifferentialAt_iff, hwi i] using hφ i
    · apply (toDualMap ℝ E).injective
      calc
        toDualMap ℝ E (∑ i : Fin m, w i) = ∑ i : Fin m, toDualMap ℝ E (w i) := by
          simp
        _ = ∑ i : Fin m, φ i := by
          simp [hwi]
        _ = toDualMap ℝ E z := hsum
  · rintro ⟨w, hw, rfl⟩
    -- Push the Euclidean summand witnesses forward and use linearity of the Riesz map.
    refine ⟨fun i : Fin m ↦ toDualMap ℝ E (w i), ?_, ?_⟩
    · intro i
      simpa [mem_euclideanSubdifferentialAt_iff] using hw i
    · exact
        (map_sum (toDualMap ℝ E) (fun i : Fin m ↦ w i) Finset.univ).symm

/-- Helper for Proposition 3.32: a finite Minkowski sum of singleton sets is again the singleton
containing the sum of the points. -/
private lemma finset_sum_singleton_eq_singleton_sum
    {ι : Type*} (s : Finset ι) (v : ι → E) :
    Finset.sum s (fun i ↦ ({v i} : Set E)) = ({Finset.sum s v} : Set E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Set.singleton_zero]
  | @insert i s hi hs =>
      -- Peel off one singleton term and fold the remaining singleton sum into one point.
      simp [Finset.sum_insert, hi, hs]

/-- Helper for Proposition 3.32: if exactly one summand is a closed ball and the others are
singletons, then the full Minkowski sum is the translate of that closed ball by the residual
singleton sum. -/
private lemma finsetSumAtSite_eq_translateClosedBall
    (v : Fin m → E) (r : ℝ) (j : Fin m) :
    (∑ i : Fin m, if i = j then closedBall (0 : E) r else ({v i} : Set E)) =
      (fun w : E ↦ (Finset.univ.erase j).sum v + w) '' closedBall (0 : E) r := by
  classical
  calc
    (∑ i : Fin m, if i = j then closedBall (0 : E) r else ({v i} : Set E))
        = Finset.sum (Finset.univ.erase j) (fun i ↦ ({v i} : Set E)) + closedBall (0 : E) r := by
          -- Split off the unique ball term at index `j`.
          calc
            (∑ i : Fin m, if i = j then closedBall (0 : E) r else ({v i} : Set E))
                = Finset.sum (Finset.univ.erase j) (fun i ↦
                    if i = j then closedBall (0 : E) r else ({v i} : Set E)) +
                    (if j = j then closedBall (0 : E) r else ({v j} : Set E)) := by
                      simpa using
                        (Finset.sum_erase_add
                          Finset.univ
                          (fun i : Fin m ↦
                            if i = j then closedBall (0 : E) r else ({v i} : Set E))
                          (Finset.mem_univ j)).symm
            _ = Finset.sum (Finset.univ.erase j) (fun i ↦ ({v i} : Set E)) +
                  closedBall (0 : E) r := by
                  congr 1
                  · refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp [(Finset.mem_erase.mp hi).1]
                  · simp
    _ = {(Finset.univ.erase j).sum v} + closedBall (0 : E) r := by
          rw [finset_sum_singleton_eq_singleton_sum]
    _ = (fun w : E ↦ (Finset.univ.erase j).sum v + w) '' closedBall (0 : E) r := by
          simp

-- Proof sketch: rewrite the weighted one-site distance `y ↦ ω * dist y a` using `dist_eq_norm`
-- into `y ↦ ω * ‖y - a‖`, then obtain its Euclidean
-- subdifferential from the affine `ℓ₂` formula and the constant-scaling rule for the
-- nonnegative weight `ω`.
/-- Helper for Proposition 3.32: for the weighted one-site term `fun y ↦ ω * dist y a` with
nonnegative weight `ω`, the Euclidean subdifferential is the singleton normalized direction away
from the site and the closed Euclidean ball `closedBall (0 : E) ω` at the site. -/
theorem euclidean_subdifferentialAt_weighted_dist_eq_piecewise
    (ω : ℝ) (hω : 0 ≤ ω) (a x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ω * dist y a) x =
      if x = a then
        closedBall (0 : E) ω
      else
        {ω • ((‖x - a‖)⁻¹ • (x - a))} := by
  have hdist :
      euclideanSubdifferentialAt (fun y : E ↦ dist y a) x =
        if x = a then
          closedBall (0 : E) 1
        else
          {(‖x - a‖)⁻¹ • (x - a)} := by
    -- Specialize the affine `ℓ₂` formula to the identity map translated by `-a`, then split
    -- into the zero and nonzero branches explicitly.
    by_cases hxa : x = a
    · subst hxa
      simpa [dist_eq_norm, sub_eq_add_neg] using
        (euclidean_subdifferentialAt_affine_l2_norm_eq_image_closedBall_of_eq_zero
          (1 : Matrix (Fin d) (Fin d) ℝ) (-x) x (by simp))
    · have hne :
          (Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ)) x + -a ≠ 0 := by
        intro hz
        apply hxa
        exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hz)
      simpa [hxa, dist_eq_norm, sub_eq_add_neg, smul_add] using
        (euclidean_subdifferentialAt_affine_l2_norm_eq_singleton_of_ne_zero
          (1 : Matrix (Fin d) (Fin d) ℝ) (-a) x hne)
  have hconvex : ConvexOn ℝ Set.univ (fun y : E ↦ dist y a) := convexOn_univ_dist a
  calc
    euclideanSubdifferentialAt (fun y : E ↦ ω * dist y a) x
        = ω • euclideanSubdifferentialAt (fun y : E ↦ dist y a) x := by
            rw [euclideanSubdifferentialAt_const_mul_eq_smul ω hω hconvex]
    _ = ω •
          (if x = a then
            closedBall (0 : E) 1
          else
            {(‖x - a‖)⁻¹ • (x - a)}) := by
            rw [hdist]
    _ = if x = a then
          closedBall (0 : E) ω
        else
          {ω • ((‖x - a‖)⁻¹ • (x - a))} := by
            -- Scale the two branches separately: the unit ball becomes radius `ω`, and the
            -- singleton branch scales pointwise.
            by_cases hxa : x = a
            · simp only [hxa, if_pos]
              rw [_root_.smul_closedBall ω (0 : E) zero_le_one, smul_zero,
                Real.norm_of_nonneg hω, mul_one]
            · simp only [hxa, if_false, Set.smul_set_singleton, smul_smul]

-- Proof sketch: rewrite `fermatWeberObjective ω a` as the finite sum of the weighted one-site
-- terms `fun y ↦ ω i * dist y (a i)` using `fermatWeberObjective_apply`. Apply the owner
-- finite-sum rule for subdifferentials, then transport each summand through the one-site bridge
-- above.
/-- Proposition 3.32: the Euclidean subdifferential of the Fermat-Weber objective
`fun x ↦ ∑ i, ω i * ‖x - a i‖` is the finite Minkowski sum of the
single-term subdifferentials, so each summand contributes the normalized
vector `ω i • ((‖x - a i‖)⁻¹ • (x - a i))` away from its
site and the closed Euclidean ball `closedBall (0 : E) (ω i)` at its site; this remains valid for
nonnegative weights, with `ω i = 0` giving the singleton `{0}` in both cases. -/
theorem euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E) (x : E) :
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x =
      ∑ i : Fin m,
        if x = a i then
          closedBall (0 : E) (ω i)
        else
          {ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := by
  have hconvex : ∀ i : Fin m, ConvexOn ℝ Set.univ (fun y : E ↦ ω i * dist y (a i)) := by
    intro i
    exact (convexOn_univ_dist (a i)).smul (hω i)
  calc
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x
        = euclideanSubdifferentialAt (fun y : E ↦ ∑ i : Fin m, ω i * dist y (a i)) x := by
            rfl
    _ = ∑ i : Fin m, euclideanSubdifferentialAt (fun y : E ↦ ω i * dist y (a i)) x := by
          rw [euclideanSubdifferentialAt_finset_sum_eq_sum
            (fun i : Fin m ↦ fun y : E ↦ ω i * dist y (a i)) x hconvex]
    _ = ∑ i : Fin m,
          if x = a i then
            closedBall (0 : E) (ω i)
          else
            {ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := by
          -- Rewrite each one-site summand with the already established piecewise formula.
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using euclidean_subdifferentialAt_weighted_dist_eq_piecewise
            (ω i) (hω i) (a i) x

-- Proof sketch: specialize the companion finite-sum formula above to a point away from every site,
-- so every summand is a singleton. The Minkowski sum of those singleton sets is the singleton
-- containing the sum of the weighted normalized displacement vectors.
/-- Consequence of Proposition 3.32: under nonnegative weights, if `x` is not one of the sites
`a i`, then
the Euclidean subdifferential of `fermatWeberObjective ω a` is the singleton containing the
weighted sum of the normalized displacement vectors. -/
theorem euclidean_subdifferentialAt_fermatWeberObjective_eq_singleton_of_not_mem_range
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E)
    (x : E) (hx : x ∉ Set.range a) :
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x =
      {∑ i : Fin m, ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := by
  have hxa : ∀ i : Fin m, x ≠ a i := by
    intro i hxi
    exact hx ⟨i, hxi.symm⟩
  calc
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x
        = ∑ i : Fin m, ({ω i • ((‖x - a i‖)⁻¹ • (x - a i))} : Set E) := by
            rw [euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise
              ω hω a x]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hxa i]
    _ = {∑ i : Fin m, ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := by
          -- Once every summand is a singleton, the whole Minkowski sum is a singleton.
          rw [finset_sum_singleton_eq_singleton_sum]

-- Proof sketch: under injectivity of the sites, the site test `a j = a i` singles out exactly
-- one nonsmooth summand in the finite-sum companion formula. Split that term off as the radius
-- `ω j` closed ball and keep the remaining singleton terms as a translated residual sum.
/-- Consequence of Proposition 3.32: under nonnegative weights and pairwise distinct sites, the
Euclidean subdifferential of `fermatWeberObjective ω a` at the site `a j` is the translate of
`closedBall (0 : E) (ω j)` by the residual weighted sum over the remaining sites. -/
theorem euclidean_subdifferentialAt_fermatWeberObjective_eq_image_closedBall_at_site
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E) (ha : Function.Injective a)
    (j : Fin m) :
    euclideanSubdifferentialAt (fermatWeberObjective ω a) (a j) =
      (fun v : E ↦
        (Finset.univ.erase j).sum
            (fun i : Fin m ↦ ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))) + v) ''
        closedBall (0 : E) (ω j) := by
  have hsplit :
      (∑ i : Fin m,
        if a j = a i then
          closedBall (0 : E) (ω i)
        else
          ({ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))} : Set E)) =
        ∑ i : Fin m,
          if i = j then
            closedBall (0 : E) (ω j)
          else
            ({ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))} : Set E) := by
    -- Injectivity converts the site test `a j = a i` into the index test `i = j`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hij : i = j
    · subst hij
      simp
    · have haji : a j ≠ a i := by
        intro hEq
        apply hij
        exact (ha hEq).symm
      simp [hij, haji]
  calc
    euclideanSubdifferentialAt (fermatWeberObjective ω a) (a j)
        = ∑ i : Fin m,
            if a j = a i then
              closedBall (0 : E) (ω i)
            else
              ({ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))} : Set E) := by
                simpa using
                  (euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise
                    ω hω a (a j))
    _ = ∑ i : Fin m,
          if i = j then
            closedBall (0 : E) (ω j)
          else
            ({ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))} : Set E) := hsplit
    _ = (fun v : E ↦
          (Finset.univ.erase j).sum
              (fun i : Fin m ↦ ω i • ((‖a j - a i‖)⁻¹ • (a j - a i))) + v) ''
          closedBall (0 : E) (ω j) := by
            -- Isolate the unique ball term and package the residual singleton sum as a
            -- translation.
            simpa using
              (finsetSumAtSite_eq_translateClosedBall
                (fun i : Fin m ↦ ω i • ((‖a j - a i‖)⁻¹ • (a j - a i)))
                (ω j) j)

end
