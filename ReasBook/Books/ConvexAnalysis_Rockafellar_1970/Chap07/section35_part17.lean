/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part16

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

-- Proof sketch: apply the one-variable differentiability criterion from Theorem 25.1 to the
-- convex slice `v' ↦ K u v'` and to the convex function `u' ↦ -K u' v`, which encodes
-- concavity in the first variable. Finite-point differentiability of the packed `EReal` map on
-- `ℝ^(m+n)` identifies a distinguished gradient vector at `(u, v)`, and the saddle inequalities
-- show that its split coordinates give the unique saddle subgradient. Conversely, uniqueness of
-- the saddle subgradient forces uniqueness of the slice subgradients, from which
-- differentiability of the packed map follows.
/-- The packed `EReal`-valued map on `ℝ^(m+n)` associated to a saddle kernel `K`. -/
def packedSaddleKernel {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z => K (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- The split gradient pair obtained from a chosen differentiability witness for the packed saddle
kernel at `(u, v)`. -/
noncomputable def packedSaddleKernelGradientPairAt {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    (Fin m → ℝ) × (Fin n → ℝ) :=
  (fun i => erealGradientAt hDiff (Fin.castAdd n i),
    fun j => erealGradientAt hDiff (Fin.natAdd m j))

/-- An extended-real saddle kernel is finite on a neighborhood of `(u, v)` when it is finite at
every point of some open neighborhood in `ℝ^m × ℝ^n`. -/
def SaddleKernelFiniteOnNeighborhoodAt {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Prop :=
  ∃ N : Set ((Fin m → ℝ) × (Fin n → ℝ)),
    IsOpen N ∧
      (u, v) ∈ N ∧
      ∀ p ∈ N, K p.1 p.2 ≠ (⊤ : EReal) ∧ K p.1 p.2 ≠ (⊥ : EReal)

/-- The directional derivative function of a saddle kernel at `(u, v)` is linear when there is a
single pair `(u*, v*)` whose Euclidean pairing gives every directional derivative. -/
def HasLinearSaddleDirectionalDerivativeAt {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Prop :=
  ∃ uStar : Fin m → ℝ,
    ∃ vStar : Fin n → ℝ,
      ∀ u' : Fin m → ℝ, ∀ v' : Fin n → ℝ,
        IsSaddleDirectionalDerivativeAt K u v u' v'
          (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * v' j) : ℝ) : EReal))

/-- Helper for Theorem 35.8: dot products split over `Fin.append`. -/
lemma helperForTheorem_35_8_dotProduct_append
    {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) (b : Fin (m + n) → ℝ) :
    dotProduct (Fin.append u v) b =
      dotProduct u (fun i => b (Fin.castAdd n i)) +
        dotProduct v (fun j => b (Fin.natAdd m j)) := by
  classical
  -- Split the dot product sum into the first `m` and last `n` coordinate blocks.
  simp [dotProduct, Fin.sum_univ_add, Fin.append, Fin.addCases]

/-- Helper for Theorem 35.8: the packed directional difference quotient along a pure second-variable
direction coincides with the one-variable directional difference quotient of the convex slice
`v' ↦ K u v'`. -/
lemma helperForTheorem_35_8_directionalDifferenceQuotient_secondSlice
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (vDir : Fin n → ℝ) (t : ℝ) :
    directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (Fin.append (0 : Fin m → ℝ) vDir) t =
      directionalDifferenceQuotientAt (K u) v vDir t := by
  -- The packed map `z ↦ K(z₁,z₂)` changes only in the `v` coordinates when the direction is
  -- `Fin.append 0 vDir`.
  -- First reduce both quotients to the same explicit pointwise update of the second block.
  have hvUpdate : v + t • vDir = (fun j : Fin n => v j + t * vDir j) := by
    funext j
    simp [Pi.add_apply, Pi.smul_apply]
  simp [packedSaddleKernel, directionalDifferenceQuotientAt, hvUpdate, Pi.add_apply, Pi.smul_apply]

/-- Helper for Theorem 35.8: along the positive ray, differentiability of the packed kernel makes
the reflected first-slice quotient eventually equal to the negative packed quotient in the
reflected axis direction. -/
lemma helperForTheorem_35_8_directionalDifferenceQuotient_reflectedFirstSlice_eventuallyEq
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uDir : Fin m → ℝ)
    (hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v))
    (huDir_ne : uDir ≠ 0) :
    Filter.EventuallyEq
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun t =>
        directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir t)
      (fun t =>
        -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
          (Fin.append (-uDir) (0 : Fin n → ℝ)) t) := by
  have hKuvFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := by
    -- Evaluating the packed kernel at `Fin.append u v` gives the base kernel value.
    simpa [packedSaddleKernel] using ERealDifferentiableAt.finiteAt hDiff
  have huAll_ne :
      (Fin.append (-uDir) (0 : Fin n → ℝ) : Fin (m + n) → ℝ) ≠ 0 := by
    -- A nonzero first block stays nonzero after appending the zero second block.
    intro hzero
    have : uDir = 0 := by
      funext i
      have hi := congrArg (fun z : Fin (m + n) → ℝ => z (Fin.castAdd n i)) hzero
      simpa [Fin.append] using hi
    exact huDir_ne this
  have hfiniteRay :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        Fin.append u v + t • Fin.append (-uDir) (0 : Fin n → ℝ) ∈
              effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (packedSaddleKernel K) ∧
          packedSaddleKernel K
              (Fin.append u v + t • Fin.append (-uDir) (0 : Fin n → ℝ)) ≠ (⊥ : EReal) := by
    -- Differentiability controls the packed kernel along every sufficiently short positive ray.
    exact
      (helperForTheorem_25_1_1_tendsto_ray_to_puncturedNeighborhood
        (x := Fin.append u v) (y := Fin.append (-uDir) (0 : Fin n → ℝ)) huAll_ne).eventually
          (ERealDifferentiableAt.eventually_finiteValuedWithin_punctured hDiff)
  filter_upwards [self_mem_nhdsWithin, hfiniteRay] with t ht htFinite
  have harg :
      -((-u) + t • uDir) = u + t • (-uDir) := by
    -- Reflecting the translated point moves the sign onto the direction.
    funext i
    simp [Pi.add_apply, Pi.smul_apply]
    ring
  have hstepTop : K (u + t • (-uDir)) v ≠ (⊤ : EReal) := by
    -- The positive-ray point is in the packed effective domain.
    have : packedSaddleKernel K
        (Fin.append u v + t • Fin.append (-uDir) (0 : Fin n → ℝ)) ≠ (⊤ : EReal) := by
      exact
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin (m + n) → ℝ))) (f := packedSaddleKernel K) htFinite.1
    simpa [packedSaddleKernel, Pi.add_apply, Pi.smul_apply] using this
  have hstepBot : K (u + t • (-uDir)) v ≠ (⊥ : EReal) := by
    -- The punctured differentiability control also excludes `⊥` on the same ray.
    simpa [packedSaddleKernel, Pi.add_apply, Pi.smul_apply] using htFinite.2
  have hnegNumerator :
      -K (u + t • (-uDir)) v - -K u v =
        -(K (u + t • (-uDir)) v - K u v) := by
    -- On finite values, the reflected slice numerator is the negative of the packed numerator.
    calc
      -K (u + t • (-uDir)) v - -K u v =
          -K (u + t • (-uDir)) v + K u v := by
            rw [sub_eq_add_neg, neg_neg]
      _ = -(K (u + t • (-uDir)) v - K u v) := by
            symm
            exact EReal.neg_sub (Or.inl hstepBot) (Or.inl hstepTop)
  have hnegNumerator' :
      -K (u + -(t • uDir)) v - -K u v =
        -(K (u + -(t • uDir)) v - K u v) := by
    -- `t • (-uDir)` simplifies to `-(t • uDir)` in the quotient expansions.
    simpa [smul_neg, add_assoc, add_left_comm, add_comm] using hnegNumerator
  -- After restricting to the finite-valued ray, both quotients are explicit negatives of the
  -- same packed numerator.
  have hReflected :
      directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir t =
        (-(K (u + -(t • uDir)) v - K u v)) / (t : EReal) := by
    -- Expand the reflected slice quotient and apply the finite-valued negation rule.
    simp [directionalDifferenceQuotientAt, harg, hnegNumerator', Pi.add_apply, Pi.smul_apply]
  have hPacked :
      directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
          (Fin.append (-uDir) (0 : Fin n → ℝ)) t =
        (K (u + -(t • uDir)) v - K u v) / (t : EReal) := by
    -- Expand the packed quotient; the direction only changes the first block.
    have huUpdate : u + -(t • uDir) = (fun i : Fin m => u i + -(t * uDir i)) := by
      funext i
      simp [Pi.add_apply, Pi.smul_apply]
    simp [directionalDifferenceQuotientAt, packedSaddleKernel, huUpdate, Pi.add_apply, Pi.smul_apply]
  -- Combine the two explicit formulas.
  rw [hReflected, hPacked]
  -- Move the outer negation onto the numerator using `div_eq_mul_inv` and `EReal.neg_mul`.
  simp [div_eq_mul_inv, EReal.neg_mul]

/-- Helper for Theorem 35.8: the packed directional quotient is exactly the saddle directional
quotient after splitting a packed direction into its `u` and `v` blocks. -/
lemma helperForTheorem_35_8_packedQuotient_eq_saddleQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (uDir : Fin m → ℝ) (vDir : Fin n → ℝ) (t : ℝ) :
    directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (Fin.append uDir vDir) t =
      saddleDirectionalDifferenceQuotientAt K u v uDir vDir t := by
  have huUpdate : u + t • uDir = (fun i : Fin m => u i + t * uDir i) := by
    funext i
    simp [Pi.add_apply, Pi.smul_apply]
  have hvUpdate : v + t • vDir = (fun j : Fin n => v j + t * vDir j) := by
    funext j
    simp [Pi.add_apply, Pi.smul_apply]
  -- The packed map and the saddle quotient evaluate the same translated point.
  simp [directionalDifferenceQuotientAt, saddleDirectionalDifferenceQuotientAt,
    packedSaddleKernel, huUpdate, hvUpdate, Pi.add_apply, Pi.smul_apply]

/-- Helper for Theorem 35.8: from differentiability of the packed saddle kernel, the split gradient
pair gives unique membership in each partial subdifferential. -/
lemma helperForTheorem_35_8_forward_unique_partial_subgradients
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    let grad : (Fin m → ℝ) × (Fin n → ℝ) :=
      packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff
    (grad.1 ∈ partialSubdifferentialInFirstVariable K u v ∧
        ∀ uStar : Fin m → ℝ, uStar ∈ partialSubdifferentialInFirstVariable K u v →
          uStar = grad.1) ∧
      (grad.2 ∈ partialSubdifferentialInSecondVariable K u v ∧
        ∀ vStar : Fin n → ℝ, vStar ∈ partialSubdifferentialInSecondVariable K u v →
          vStar = grad.2) := by
  classical
  intro grad
  -- Write the packed gradient vector and its two blocks.
  let gAll : Fin (m + n) → ℝ := erealGradientAt hDiff
  let uStar : Fin m → ℝ := fun i => gAll (Fin.castAdd n i)
  let vStar : Fin n → ℝ := fun j => gAll (Fin.natAdd m j)
  have hgrad_def : grad = (uStar, vStar) := by
    -- This is just the definition of `packedSaddleKernelGradientPairAt`.
    rfl
  have hKuvFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := by
    -- Evaluating the packed kernel at `Fin.append u v` recovers the original base value `K u v`.
    simpa [packedSaddleKernel] using (ERealDifferentiableAt.finiteAt hDiff)
  have hRefFinite :
      (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊤ : EReal) ∧
        (fun x : Fin m → ℝ => -K (-x) v) (-u) ≠ (⊥ : EReal) := by
    -- Negating a finite `EReal` value swaps the top and bottom exclusions.
    exact ⟨by simpa using hKuvFinite.2, by simpa using hKuvFinite.1⟩

  -- **Second slice** `v' ↦ K u v'`: identify its upper directional derivative with `⟪vStar, vDir⟫`.
  have hSecondDir :
      ∀ vDir : Fin n → ℝ,
        upperDirectionalDerivativeAt (K u) v vDir =
          (((dotProduct vStar vDir : ℝ) : ℝ) : EReal) := by
    intro vDir
    by_cases hvDir0 : vDir = 0
    · -- The zero-direction derivative vanishes for every convex function.
      have hconv : ConvexFunction (K u) := hK.2 u
      -- Extract `D 0 = 0` from the directional-derivative package.
      rcases convex_directionalDerivative_monotone_exists_and_sublinear (K u) hconv v hKuvFinite with
        ⟨_hmono, _hpos, _hconv', hzero, _hsymm⟩
      simp [hvDir0, hzero]
    · -- For nonzero directions, compare the slice quotient against the packed quotient.
      have hconv : ConvexFunction (K u) := hK.2 u
      have hright :
          Filter.Tendsto (directionalDifferenceQuotientAt (K u) v vDir)
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds (upperDirectionalDerivativeAt (K u) v vDir)) :=
        (convex_directionalDerivative_monotone_exists_and_sublinear (K u) hconv v hKuvFinite).1 vDir
          |>.2.1
      -- Transport the packed directional quotient limit into the slice direction.
      have hvAll_ne :
          (Fin.append (0 : Fin m → ℝ) vDir : Fin (m + n) → ℝ) ≠ 0 := by
        intro hzero
        have : vDir = 0 := by
          funext j
          have := congrArg (fun z : Fin (m + n) → ℝ => z (Fin.natAdd m j)) hzero
          simpa [Fin.append] using this
        exact hvDir0 this
      have hpacked :
          Filter.Tendsto
            (directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
              (Fin.append (0 : Fin m → ℝ) vDir))
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds ((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (0 : Fin m → ℝ) vDir) : ℝ) : EReal))) :=
        ERealDifferentiableAt.tendsto_directionalDifferenceQuotient (hf := hDiff)
          (y := (Fin.append (0 : Fin m → ℝ) vDir)) hvAll_ne
      have hslice :
          Filter.Tendsto (directionalDifferenceQuotientAt (K u) v vDir)
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds ((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (0 : Fin m → ℝ) vDir) : ℝ) : EReal))) := by
        -- The packed and slice quotients agree pointwise.
        refine Filter.Tendsto.congr' ?_ hpacked
        filter_upwards with t
        simpa using
          (helperForTheorem_35_8_directionalDifferenceQuotient_secondSlice
            (K := K) u v vDir t)
      -- Identifying the two limits pins down the upper directional derivative.
      have hlimEq :
          upperDirectionalDerivativeAt (K u) v vDir =
            ((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (0 : Fin m → ℝ) vDir) : ℝ) : EReal)) :=
        tendsto_nhds_unique hright hslice
      -- Rewrite the packed dot product as the `vStar` dot product.
      have hdot :
          ((erealGradientAt hDiff) ⬝ᵥ (Fin.append (0 : Fin m → ℝ) vDir) : ℝ) =
            dotProduct vStar vDir := by
        -- Split the dot product over the `Fin.append` block coordinates.
        have hsplit :=
          helperForTheorem_35_8_dotProduct_append (m := m) (n := n)
            (u := (0 : Fin m → ℝ)) (v := vDir) (b := gAll)
        calc
          dotProduct gAll (Fin.append (0 : Fin m → ℝ) vDir) =
              dotProduct (Fin.append (0 : Fin m → ℝ) vDir) gAll := by
                rw [dotProduct_comm]
          _ = dotProduct (0 : Fin m → ℝ) (fun i => gAll (Fin.castAdd n i)) +
                dotProduct vDir (fun j => gAll (Fin.natAdd m j)) := by
                simpa using hsplit
          _ = dotProduct vStar vDir := by
                simp [vStar, dotProduct_comm]
      simpa [hdot] using hlimEq

  -- **First slice** `x ↦ -K (-x) v`: identify its upper directional derivative with `⟪uStar, uDir⟫`.
  have hFirstDir :
      ∀ uDir : Fin m → ℝ,
        upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir =
          (((dotProduct uStar uDir : ℝ) : ℝ) : EReal) := by
    intro uDir
    by_cases huDir0 : uDir = 0
    · -- Zero direction.
      have hconv : ConvexFunction (fun x : Fin m → ℝ => -K (-x) v) :=
        helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
      rcases
          convex_directionalDerivative_monotone_exists_and_sublinear
            (fun x : Fin m → ℝ => -K (-x) v) hconv (-u) hRefFinite with
        ⟨_hmono, _hpos, _hconv', hzero, _hsymm⟩
      simp [huDir0, hzero]
    · -- Nonzero direction: compare the reflected slice quotient against the packed quotient.
      have hconv : ConvexFunction (fun x : Fin m → ℝ => -K (-x) v) :=
        helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
      have hright :
          Filter.Tendsto
            (directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir)
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds (upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir)) :=
        (convex_directionalDerivative_monotone_exists_and_sublinear
          (fun x : Fin m → ℝ => -K (-x) v) hconv (-u) hRefFinite).1 uDir |>.2.1
      have huAll_ne :
          (Fin.append (-uDir) (0 : Fin n → ℝ) : Fin (m + n) → ℝ) ≠ 0 := by
        intro hzero
        have : uDir = 0 := by
          funext i
          have := congrArg (fun z : Fin (m + n) → ℝ => z (Fin.castAdd n i)) hzero
          simpa [Fin.append] using this
        exact huDir0 this
      have hpacked :
          Filter.Tendsto
            (directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
              (Fin.append (-uDir) (0 : Fin n → ℝ)))
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds ((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (-uDir) (0 : Fin n → ℝ)) : ℝ) : EReal))) :=
        ERealDifferentiableAt.tendsto_directionalDifferenceQuotient (hf := hDiff)
          (y := (Fin.append (-uDir) (0 : Fin n → ℝ))) huAll_ne
      have hreflected :
          Filter.Tendsto
            (directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir)
            (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
            (nhds (-((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (-uDir) (0 : Fin n → ℝ)) : ℝ) : EReal)))) := by
        -- Route correction: the reflected quotient identity only holds on the positive ray where
        -- packed differentiability guarantees finite values, so we use eventual equality there.
        refine Filter.Tendsto.congr' ?_ (Filter.Tendsto.neg hpacked)
        simpa using
          (helperForTheorem_35_8_directionalDifferenceQuotient_reflectedFirstSlice_eventuallyEq
            (K := K) u v uDir hDiff huDir0).symm
      have hlimEq :
          upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir =
            -((((erealGradientAt hDiff) ⬝ᵥ (Fin.append (-uDir) (0 : Fin n → ℝ)) : ℝ) : EReal)) :=
        tendsto_nhds_unique hright hreflected
      have hdot :
          ((erealGradientAt hDiff) ⬝ᵥ (Fin.append (-uDir) (0 : Fin n → ℝ)) : ℝ) =
            -dotProduct uStar uDir := by
        -- Again split the dot product over `Fin.append`, then simplify using the zero block.
        have hsplit :=
          helperForTheorem_35_8_dotProduct_append (m := m) (n := n)
            (u := (-uDir)) (v := (0 : Fin n → ℝ)) (b := gAll)
        calc
          dotProduct gAll (Fin.append (-uDir) (0 : Fin n → ℝ)) =
              dotProduct (Fin.append (-uDir) (0 : Fin n → ℝ)) gAll := by
                rw [dotProduct_comm]
          _ = dotProduct (-uDir) (fun i => gAll (Fin.castAdd n i)) +
                dotProduct (0 : Fin n → ℝ) (fun j => gAll (Fin.natAdd m j)) := by
                simpa using hsplit
          _ = -dotProduct uStar uDir := by
                simp [uStar, dotProduct_comm, dotProduct_neg]
      -- Put the sign into the final formula.
      simpa [hdot, neg_neg] using hlimEq

  -- Now invoke the Chapter 25 uniqueness lemma on each convex slice.
  have huniqFirst :
      ∃! w : Fin m → ℝ,
        IsSubgradientAt (fun x : Fin m → ℝ => -K (-x) v) (-u)
          (dotProductEquiv ℝ (Fin m) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := fun x : Fin m → ℝ => -K (-x) v)
      (hf := helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v)
      (x := -u) (hx := hRefFinite)
      (g := uStar) hFirstDir
  have huniqSecond :
      ∃! w : Fin n → ℝ,
        IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := K u) (hf := hK.2 u) (x := v) (hx := hKuvFinite)
      (g := vStar) hSecondDir
  rcases huniqFirst with ⟨u0, hu0, huuniq⟩
  rcases huniqSecond with ⟨v0, hv0, hvuniq⟩
  -- Identify the unique vectors with the split gradient blocks.
  have hu0Eq : u0 = uStar := by
    -- `uStar` itself is a subgradient by construction of `huniqFirst`.
    have huStarSub :
        IsSubgradientAt (fun x : Fin m → ℝ => -K (-x) v) (-u)
          (dotProductEquiv ℝ (Fin m) uStar) := by
      -- Reuse the same construction as `helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative`.
      have hiff :=
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (fun x : Fin m → ℝ => -K (-x) v)
          (helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v)
          (-u) hRefFinite (dotProductEquiv ℝ (Fin m) uStar)).1
      apply hiff.mpr
      intro y
      -- The lower bound is an equality by `hFirstDir`.
      simpa [hFirstDir y]
    exact (huuniq uStar huStarSub).symm
  have hv0Eq : v0 = vStar := by
    have hvStarSub :
        IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) vStar) := by
      have hiff :=
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          (K u) (hK.2 u) v hKuvFinite (dotProductEquiv ℝ (Fin n) vStar)).1
      apply hiff.mpr
      intro y
      simpa [hSecondDir y]
    exact (hvuniq vStar hvStarSub).symm

  -- Translate subgradient uniqueness back to partial-subdifferential uniqueness.
  have huStar_mem : uStar ∈ partialSubdifferentialInFirstVariable K u v := by
    -- Use the reflected-slice equivalence lemma.
    have : dotProductEquiv ℝ (Fin m) uStar ∈ subdifferentialAt (fun x : Fin m → ℝ => -K (-x) v) (-u) := by
      -- `hu0` is the unique subgradient, and we have shown it equals `uStar`.
      have : IsSubgradientAt (fun x : Fin m → ℝ => -K (-x) v) (-u)
          (dotProductEquiv ℝ (Fin m) uStar) := by
        simpa [hu0Eq] using hu0
      exact this
    -- Apply the bridge `↔` to land in `partialSubdifferentialInFirstVariable`.
    have := (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
      (K := K) (u := u) (v := v) (uStar := uStar)).1 (by simpa [subdifferentialAt] using this)
    exact this
  have hvStar_mem : vStar ∈ partialSubdifferentialInSecondVariable K u v := by
    have : dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt (K u) v := by
      have : IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) vStar) := by
        simpa [hv0Eq] using hv0
      simpa [subdifferentialAt] using this
    exact (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
      (K := K) (u := u) (v := v) (vStar := vStar)).1
        (by simpa using this)
  have huStar_unique :
      ∀ uStar' : Fin m → ℝ, uStar' ∈ partialSubdifferentialInFirstVariable K u v →
        uStar' = uStar := by
    intro uStar' huStar'
    have : dotProductEquiv ℝ (Fin m) uStar' ∈ subdifferentialAt (fun x : Fin m → ℝ => -K (-x) v) (-u) := by
      -- Bridge membership back to the reflected slice.
      have :=
        (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
          (K := K) (u := u) (v := v) (uStar := uStar')).2 huStar'
      simpa [subdifferentialAt] using this
    -- Uniqueness of subgradients in the reflected slice forces `uStar' = uStar`.
    have huEq : uStar' = u0 := huuniq uStar' (by simpa [subdifferentialAt] using this)
    simpa [hu0Eq] using huEq
  have hvStar_unique :
      ∀ vStar' : Fin n → ℝ, vStar' ∈ partialSubdifferentialInSecondVariable K u v →
        vStar' = vStar := by
    intro vStar' hvStar'
    have : dotProductEquiv ℝ (Fin n) vStar' ∈ subdifferentialAt (K u) v := by
      have :=
        (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
          (K := K) (u := u) (v := v) (vStar := vStar')).2 hvStar'
      simpa [subdifferentialAt] using this
    have hvEq : vStar' = v0 := hvuniq vStar' (by simpa [subdifferentialAt] using this)
    simpa [hv0Eq] using hvEq

  -- Finally rewrite everything back in terms of `grad`.
  have huMem : grad.1 ∈ partialSubdifferentialInFirstVariable K u v := by
    simpa [hgrad_def] using huStar_mem
  have hvMem : grad.2 ∈ partialSubdifferentialInSecondVariable K u v := by
    simpa [hgrad_def] using hvStar_mem
  have huUniq :
      ∀ uStar' : Fin m → ℝ, uStar' ∈ partialSubdifferentialInFirstVariable K u v → uStar' = grad.1 := by
    intro uStar' huStar'
    have : uStar' = uStar := huStar_unique uStar' huStar'
    simpa [hgrad_def] using this
  have hvUniq :
      ∀ vStar' : Fin n → ℝ, vStar' ∈ partialSubdifferentialInSecondVariable K u v → vStar' = grad.2 := by
    intro vStar' hvStar'
    have : vStar' = vStar := hvStar_unique vStar' hvStar'
    simpa [hgrad_def] using this
  exact ⟨⟨huMem, huUniq⟩, ⟨hvMem, hvUniq⟩⟩

/-- Helper for Theorem 35.8: uniqueness in the product subdifferential implies each partial
subdifferential is a singleton. -/
lemma helperForTheorem_35_8_unique_productSubgradient_gives_unique_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (huniq :
      ∃! g : (Fin m → ℝ) × (Fin n → ℝ), g ∈ productSubdifferentialAt K u v) :
    ∃ uStar : Fin m → ℝ, ∃ vStar : Fin n → ℝ,
      partialSubdifferentialInFirstVariable K u v = {uStar} ∧
        partialSubdifferentialInSecondVariable K u v = {vStar} := by
  classical
  rcases huniq with ⟨g0, hg0, hguniq⟩
  refine ⟨g0.1, g0.2, ?_, ?_⟩
  · -- First component set is a singleton.
    ext uStar
    constructor
    · intro huStar
      have : (uStar, g0.2) ∈ productSubdifferentialAt K u v := by
        exact ⟨huStar, hg0.2⟩
      have hEq : (uStar, g0.2) = g0 := hguniq (uStar, g0.2) this
      simpa using congrArg Prod.fst hEq
    · intro huStar
      have : uStar = g0.1 := by simpa using huStar
      simpa [this] using hg0.1
  · -- Second component set is a singleton.
    ext vStar
    constructor
    · intro hvStar
      have : (g0.1, vStar) ∈ productSubdifferentialAt K u v := by
        exact ⟨hg0.1, hvStar⟩
      have hEq : (g0.1, vStar) = g0 := hguniq (g0.1, vStar) this
      simpa using congrArg Prod.snd hEq
    · intro hvStar
      have : vStar = g0.2 := by simpa using hvStar
      simpa [this] using hg0.2

/-- Helper for Theorem 35.8: a singleton first partial subdifferential is immediately nonempty and
bounded. -/
lemma helperForTheorem_35_8_nonempty_bounded_partialFirst_of_singleton
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {uStar : Fin m → ℝ}
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar}) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  constructor
  · -- Rewriting by the singleton description gives a concrete witness at once.
    refine ⟨uStar, ?_⟩
    simpa [hFirstSingleton]
  · -- A singleton subset of a normed space is bounded.
    simpa [hFirstSingleton] using (Bornology.isBounded_singleton uStar)

/-- Helper for Theorem 35.8: a singleton second partial subdifferential is immediately nonempty and
bounded. -/
lemma helperForTheorem_35_8_nonempty_bounded_partialSecond_of_singleton
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {vStar : Fin n → ℝ}
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    Set.Nonempty (partialSubdifferentialInSecondVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) := by
  constructor
  · -- Rewriting by the singleton description gives a concrete witness at once.
    refine ⟨vStar, ?_⟩
    simpa [hSecondSingleton]
  · -- A singleton subset of a normed space is bounded.
    simpa [hSecondSingleton] using (Bornology.isBounded_singleton vStar)

/-- Helper for Theorem 35.8: a singleton first partial subdifferential already fixes the
first-axis saddle directional derivative value in every direction. -/
lemma helperForTheorem_35_8_firstAxisDirectionalDerivative_value_of_singleton_partial
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {uStar : Fin m → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (uDir : Fin m → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v uDir 0 L} =
      ((((∑ i : Fin m, uStar i * uDir i) : ℝ) : EReal)) := by
  have hFirstData :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) :=
    helperForTheorem_35_8_nonempty_bounded_partialFirst_of_singleton
      (K := K) (u := u) (v := v) hFirstSingleton
  -- The first-direction support formula is already exact once the partial set is a singleton.
  simpa [hFirstSingleton] using
    helperForText_35_6_10_formula_of_nonempty_bounded_partialFirst
      (K := K) (u := u) (v := v) hK hFinite hFirstData.1 hFirstData.2 uDir

/-- Helper for Theorem 35.8: a singleton second partial subdifferential already fixes the
second-axis saddle directional derivative value in every direction. -/
lemma helperForTheorem_35_8_secondAxisDirectionalDerivative_value_of_singleton_partial
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar})
    (vDir : Fin n → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 vDir L} =
      ((((∑ j : Fin n, vStar j * vDir j) : ℝ) : EReal)) := by
  have hSecondData :
      Set.Nonempty (partialSubdifferentialInSecondVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) :=
    helperForTheorem_35_8_nonempty_bounded_partialSecond_of_singleton
      (K := K) (u := u) (v := v) hSecondSingleton
  -- The second-direction support formula likewise collapses to the singleton pairing value.
  simpa [hSecondSingleton] using
    helperForText_35_6_11_formula_of_nonempty_bounded_partialSecond
      (K := K) (u := u) (v := v) hK hFinite hSecondData.1 hSecondData.2 vDir

/-- Helper for Theorem 35.8: singleton partial subdifferentials force differentiability of the
reflected first slice and of the honest second slice, so both one-variable slices have interior
finite base points. -/
lemma helperForTheorem_35_8_sliceDifferentiabilityWitnesses_of_singleton_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ERealDifferentiableAt (fun x : Fin m → ℝ => -K (-x) v) (-u) ∧
      ERealDifferentiableAt (K u) v := by
  let f : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  let g : (Fin n → ℝ) → EReal := K u
  have hf : ConvexFunction f := by
    -- The reflected first slice is convex because `K` is concave in the first variable.
    simpa [f] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves a convex second slice.
    simpa [g] using hK.2 u
  have hfu : f (-u) ≠ (⊤ : EReal) ∧ f (-u) ≠ (⊥ : EReal) := by
    -- The reflected base value is finite exactly when `K u v` is finite.
    simpa [f] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hFinite
  have hgu : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The honest second slice has the same finite base value.
    simpa [g] using hFinite
  have huStar_mem : uStar ∈ partialSubdifferentialInFirstVariable K u v := by
    -- Rewriting the singleton description gives the canonical first partial witness.
    simpa [hFirstSingleton]
  have hvStar_mem : vStar ∈ partialSubdifferentialInSecondVariable K u v := by
    -- The second partial witness is equally canonical.
    simpa [hSecondSingleton]
  have huStar_subgradient :
      IsSubgradientAt f (-u) (dotProductEquiv ℝ (Fin m) uStar) := by
    -- Translate the textbook first partial into a subgradient of the reflected slice.
    have hmem :
        dotProductEquiv ℝ (Fin m) uStar ∈ subdifferentialAt f (-u) :=
      (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
        (K := K) (u := u) (v := v) (uStar := uStar)).2 huStar_mem
    simpa [f, subdifferentialAt] using hmem
  have hvStar_subgradient :
      IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) vStar) := by
    -- Translate the textbook second partial into a subgradient of the convex slice.
    have hmem :
        dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt g v :=
      (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
        (K := K) (u := u) (v := v) (vStar := vStar)).2 hvStar_mem
    simpa [g, subdifferentialAt] using hmem
  have huStar_unique :
      ∀ w : Fin m → ℝ, IsSubgradientAt f (-u) (dotProductEquiv ℝ (Fin m) w) → w = uStar := by
    intro w hw
    -- Any reflected-slice subgradient transports back into the singleton first partial.
    have hwMem : w ∈ partialSubdifferentialInFirstVariable K u v := by
      exact
        (helperForText_35_6_6_reflectedSliceSubgradient_iff_partialFirstMem
          (K := K) (u := u) (v := v) (uStar := w)).1
          (by simpa [f, subdifferentialAt] using hw)
    simpa [hFirstSingleton] using hwMem
  have hvStar_unique :
      ∀ w : Fin n → ℝ, IsSubgradientAt g v (dotProductEquiv ℝ (Fin n) w) → w = vStar := by
    intro w hw
    -- The same singleton transport works for the honest second slice.
    have hwMem : w ∈ partialSubdifferentialInSecondVariable K u v := by
      exact
        (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
          (K := K) (u := u) (v := v) (vStar := w)).1
          (by simpa [g, subdifferentialAt] using hw)
    simpa [hSecondSingleton] using hwMem
  have hRefDiff : ERealDifferentiableAt f (-u) := by
    -- Theorem 25.1 turns the unique reflected-slice subgradient into differentiability.
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hf (-u) hfu).2 ?_
    exact ⟨uStar, huStar_subgradient, huStar_unique⟩
  have hSecondDiff : ERealDifferentiableAt g v := by
    -- The honest second slice is handled by the same one-variable theorem.
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        g hg v hgu).2 ?_
    exact ⟨vStar, hvStar_subgradient, hvStar_unique⟩
  exact ⟨hRefDiff, hSecondDiff⟩

/-- Helper for Theorem 35.8: singleton partial subdifferentials already produce open convex
neighborhoods on which the first slice `x ↦ K x v` and the second slice `y ↦ K u y` are finite. -/
lemma helperForTheorem_35_8_sliceFiniteNeighborhoods_of_singleton_partials
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
        (∀ x ∈ C, K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal)) ∧
      IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
        (∀ y ∈ D, K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal)) := by
  let f : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  let g : (Fin n → ℝ) → EReal := K u
  have hf : ConvexFunction f := by
    -- The reflected first slice is convex.
    simpa [f] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hK v
  have hg : ConvexFunction g := by
    -- The second slice is convex.
    simpa [g] using hK.2 u
  rcases
      helperForTheorem_35_8_sliceDifferentiabilityWitnesses_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFirstSingleton hSecondSingleton with
    ⟨hRefDiff, hSecondDiff⟩
  have hRefProperInt :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f ∧
        (-u) ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) :=
    convexFunction_proper_and_mem_interior_of_differentiableAt f hf (-u) hRefDiff
  have hSecondProperInt :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g ∧
        v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :=
    convexFunction_proper_and_mem_interior_of_differentiableAt g hg v hSecondDiff
  have hRefBallNhds :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) f ∈ nhds (-u) :=
    mem_interior_iff_mem_nhds.mp hRefProperInt.2
  have hSecondBallNhds :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∈ nhds v :=
    mem_interior_iff_mem_nhds.mp hSecondProperInt.2
  rcases Metric.mem_nhds_iff.mp hRefBallNhds with ⟨εC, hεC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp hSecondBallNhds with ⟨εD, hεD, hBallD⟩
  let C : Set (Fin m → ℝ) := Metric.ball u εC
  let D : Set (Fin n → ℝ) := Metric.ball v εD
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Open balls give the first slice neighborhood.
    simpa [C] using isOpen_ball
  · -- The center lies in its own positive-radius ball.
    simpa [C, Metric.mem_ball] using hεC
  · -- Balls are convex in finite-dimensional Euclidean spaces.
    simpa [C] using convex_ball u εC
  · intro x hx
    -- Membership in the reflected slice effective domain gives `K x v ≠ ⊥`, while properness of
    -- the reflected slice supplies `K x v ≠ ⊤`.
    have hxDist : dist x u < εC := by
      simpa [C, Metric.mem_ball] using hx
    have hxNegBall : -x ∈ Metric.ball (-u) εC := by
      simpa [Metric.mem_ball] using hxDist
    have hxDom : -x ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) f := hBallC hxNegBall
    have hxNeBot : K x v ≠ (⊥ : EReal) := by
      simpa [f, effectiveDomain_eq, lt_top_iff_ne_top] using hxDom
    have hxNeTop : K x v ≠ (⊤ : EReal) := by
      have : f (-x) ≠ (⊥ : EReal) := hRefProperInt.1.2.2 (-x) (by simp)
      simpa [f] using this
    exact ⟨hxNeTop, hxNeBot⟩
  · -- Open balls also give the second slice neighborhood.
    simpa [D] using isOpen_ball
  · -- Its center lies in the ball as well.
    simpa [D, Metric.mem_ball] using hεD
  · -- And the second ball is convex for the same reason.
    simpa [D] using convex_ball v εD
  · intro y hy
    -- Here effective-domain membership gives `K u y ≠ ⊤`, while properness excludes `⊥`.
    have hyDom : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
      exact hBallD (by simpa [D, Metric.mem_ball] using hy)
    have hyNeTop : K u y ≠ (⊤ : EReal) := by
      simpa [g, effectiveDomain_eq, lt_top_iff_ne_top] using hyDom
    have hyNeBot : K u y ≠ (⊥ : EReal) := by
      simpa [g] using hSecondProperInt.1.2.2 y (by simp)
    exact ⟨hyNeTop, hyNeBot⟩

/-- Helper for Theorem 35.8: singleton partial subdifferentials should force `(u, v)` to lie in
the interior of the full saddle effective domain. -/
lemma helperForTheorem_35_8_reflection_mem_ball
    {k : ℕ} {c x : Fin k → ℝ} {ε : ℝ}
    (hx : x ∈ Metric.ball c ε) :
    (2 • c - x) ∈ Metric.ball c ε := by
  -- Reflection across the center preserves the distance to that center.
  have hxDist : dist x c < ε := by
    simpa [Metric.mem_ball] using hx
  have hdist : dist (2 • c - x) c = dist x c := by
    rw [dist_eq_norm, dist_eq_norm]
    have hEq : (2 • c - x) - c = c - x := by
      ext i
      simp [two_smul, sub_eq_add_neg]
      ring
    rw [hEq]
    exact norm_sub_rev _ _
  rw [Metric.mem_ball, hdist]
  exact hxDist

/-- Helper for Theorem 35.8: a point and its reflection across `c` have midpoint `c`. -/
lemma helperForTheorem_35_8_midpoint_reflection_eq_center
    {k : ℕ} (c x : Fin k → ℝ) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (2 • c - x) = c := by
  -- The reflected pair is symmetric around `c`, so their midpoint is exactly `c`.
  ext i
  simp [two_smul, sub_eq_add_neg]
  ring

/-- Helper for Theorem 35.8: if a convex slice has value `⊥` at one endpoint of a reflected pair
and its midpoint value is not `⊥`, then the opposite endpoint must be `⊤`. -/
lemma helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
    {k : ℕ}
    {g : (Fin k → ℝ) → EReal} {x y m : Fin k → ℝ}
    (hConv : ConvexFunction g)
    (hMid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = m)
    (hmNeBot : g m ≠ (⊥ : EReal))
    (hxBot : g x = (⊥ : EReal)) :
    g y = (⊤ : EReal) := by
  by_cases hyTop : g y = (⊤ : EReal)
  · -- If the opposite endpoint is already `⊤`, there is nothing left to prove.
    exact hyTop
  -- Otherwise the Chapter 33 convex epigraph collapse forces the midpoint down to `⊥`.
  have hMidBot :=
    helperForLemma33_0_5_convexFunction_leftBot_rightNotTop_forces_comboBot
      (hConvFun := hConv)
      (a := (1 / 2 : ℝ))
      (b := (1 / 2 : ℝ))
      (ha := by norm_num)
      (hb := by norm_num)
      (hab := by norm_num)
      (hPosA := by norm_num)
      (hxBot := hxBot)
      (hyNeTop := hyTop)
  have : g m = (⊥ : EReal) := by
    rw [← hMid]
    exact hMidBot
  exact False.elim (hmNeBot this)

/-- Helper for Theorem 35.8: if one corner of the reflected rectangle is `⊤`, the alternating
convexity/concavity midpoint argument forces the three other corners into the checkerboard
pattern `⊥, ⊤, ⊥`. -/
lemma helperForTheorem_35_8_topCorner_forces_checkerboard
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hxvFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal))
    (hxRefvFinite : K (2 • u - x) v ≠ (⊤ : EReal) ∧ K (2 • u - x) v ≠ (⊥ : EReal))
    (huyFinite : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal))
    (huyRefFinite : K u (2 • v - y) ≠ (⊤ : EReal) ∧ K u (2 • v - y) ≠ (⊥ : EReal))
    (hxyTop : K x y = (⊤ : EReal)) :
    K (2 • u - x) y = (⊥ : EReal) ∧
      K (2 • u - x) (2 • v - y) = (⊤ : EReal) ∧
      K x (2 • v - y) = (⊥ : EReal) := by
  let gFirst : (Fin m → ℝ) → EReal := fun z => -K z y
  have hxRefyTop : gFirst (2 • u - x) = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gFirst) (x := x) (y := 2 • u - x) (m := u)
      (hConv := hK.1 y)
      (hMid := helperForTheorem_35_8_midpoint_reflection_eq_center u x)
      (hmNeBot := by simpa [gFirst] using huyFinite.1)
      (hxBot := by simpa [gFirst, hxyTop])
  have hxRefyBot : K (2 • u - x) y = (⊥ : EReal) := by
    -- Negating the reflected first slice converts the top value back to `K = ⊥`.
    simpa [gFirst] using hxRefyTop
  let gSecond : (Fin n → ℝ) → EReal := K (2 • u - x)
  have hxRefyRefTop : gSecond (2 • v - y) = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gSecond) (x := y) (y := 2 • v - y) (m := v)
      (hConv := hK.2 (2 • u - x))
      (hMid := helperForTheorem_35_8_midpoint_reflection_eq_center v y)
      (hmNeBot := hxRefvFinite.2)
      (hxBot := by simpa [gSecond] using hxRefyBot)
  have hxRefyRefTop' : K (2 • u - x) (2 • v - y) = (⊤ : EReal) := by
    -- The reflected second slice now reaches `⊤` at the opposite corner.
    simpa [gSecond] using hxRefyRefTop
  let gFirstRef : (Fin m → ℝ) → EReal := fun z => -K z (2 • v - y)
  have hxyRefTop : gFirstRef x = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gFirstRef) (x := 2 • u - x) (y := x) (m := u)
      (hConv := hK.1 (2 • v - y))
      (hMid := by
        simpa [add_comm] using helperForTheorem_35_8_midpoint_reflection_eq_center u x)
      (hmNeBot := by simpa [gFirstRef] using huyRefFinite.1)
      (hxBot := by simpa [gFirstRef] using hxRefyRefTop')
  have hxyRefBot : K x (2 • v - y) = (⊥ : EReal) := by
    -- Negating again identifies the final corner as `⊥`.
    simpa [gFirstRef] using hxyRefTop
  exact ⟨hxRefyBot, hxRefyRefTop', hxyRefBot⟩

/-- Helper for Theorem 35.8: if one corner of the reflected rectangle is `⊥`, the same midpoint
propagation yields the opposite checkerboard pattern `⊤, ⊥, ⊤`. -/
lemma helperForTheorem_35_8_botCorner_forces_checkerboard
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin n → ℝ}
    (hxvFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal))
    (hxRefvFinite : K (2 • u - x) v ≠ (⊤ : EReal) ∧ K (2 • u - x) v ≠ (⊥ : EReal))
    (huyFinite : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal))
    (huyRefFinite : K u (2 • v - y) ≠ (⊤ : EReal) ∧ K u (2 • v - y) ≠ (⊥ : EReal))
    (hxyBot : K x y = (⊥ : EReal)) :
    K (2 • u - x) y = (⊤ : EReal) ∧
      K (2 • u - x) (2 • v - y) = (⊥ : EReal) ∧
      K x (2 • v - y) = (⊤ : EReal) := by
  let gSecond : (Fin n → ℝ) → EReal := K x
  have hxyRefTop : gSecond (2 • v - y) = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gSecond) (x := y) (y := 2 • v - y) (m := v)
      (hConv := hK.2 x)
      (hMid := helperForTheorem_35_8_midpoint_reflection_eq_center v y)
      (hmNeBot := hxvFinite.2)
      (hxBot := by simpa [gSecond] using hxyBot)
  have hxyRefTop' : K x (2 • v - y) = (⊤ : EReal) := by
    -- The second-variable convex slice propagates `⊥` to `⊤` across the reflection.
    simpa [gSecond] using hxyRefTop
  let gFirstRef : (Fin m → ℝ) → EReal := fun z => -K z (2 • v - y)
  have hxRefyRefTop : gFirstRef (2 • u - x) = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gFirstRef) (x := x) (y := 2 • u - x) (m := u)
      (hConv := hK.1 (2 • v - y))
      (hMid := helperForTheorem_35_8_midpoint_reflection_eq_center u x)
      (hmNeBot := by simpa [gFirstRef] using huyRefFinite.1)
      (hxBot := by simpa [gFirstRef] using hxyRefTop')
  have hxRefyRefBot : K (2 • u - x) (2 • v - y) = (⊥ : EReal) := by
    -- Undo the negation in the reflected first slice.
    simpa [gFirstRef] using hxRefyRefTop
  let gSecondRef : (Fin n → ℝ) → EReal := K (2 • u - x)
  have hxRefyTop : gSecondRef y = (⊤ : EReal) :=
    helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
      (g := gSecondRef) (x := 2 • v - y) (y := y) (m := v)
      (hConv := hK.2 (2 • u - x))
      (hMid := by
        simpa [add_comm] using helperForTheorem_35_8_midpoint_reflection_eq_center v y)
      (hmNeBot := hxRefvFinite.2)
      (hxBot := by simpa [gSecondRef] using hxRefyRefBot)
  have hxRefyTop' : K (2 • u - x) y = (⊤ : EReal) := by
    -- The last convexity step closes the bottom-corner checkerboard pattern.
    simpa [gSecondRef] using hxRefyTop
  exact ⟨hxRefyTop', hxRefyRefBot, hxyRefTop'⟩

lemma helperForTheorem_35_8_finiteRectangle_from_sliceFiniteNeighborhoods
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {C0 : Set (Fin m → ℝ)} {D0 : Set (Fin n → ℝ)}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hC0open : IsOpen C0) (huC0 : u ∈ C0)
    (hD0open : IsOpen D0) (hvD0 : v ∈ D0)
    (hFirstFinite : ∀ x ∈ C0, K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal))
    (hSecondFinite : ∀ y ∈ D0, K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal))
    (hCornerFinite :
      ∀ {x : Fin m → ℝ} {y : Fin n → ℝ},
        K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal) →
          K (2 • u - x) v ≠ (⊤ : EReal) ∧ K (2 • u - x) v ≠ (⊥ : EReal) →
            K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal) →
              K u (2 • v - y) ≠ (⊤ : EReal) ∧ K u (2 • v - y) ≠ (⊥ : EReal) →
                K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal)) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
      IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
        ∀ x ∈ C, ∀ y ∈ D, K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal) := by
  rcases Metric.mem_nhds_iff.mp (hC0open.mem_nhds huC0) with ⟨εC, hεC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp (hD0open.mem_nhds hvD0) with ⟨εD, hεD, hBallD⟩
  let ε : ℝ := min εC εD
  let C : Set (Fin m → ℝ) := Metric.ball u ε
  let D : Set (Fin n → ℝ) := Metric.ball v ε
  have hε : 0 < ε := lt_min hεC hεD
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The direct bridge uses smaller symmetric balls around `u` and `v`.
    simpa [C] using isOpen_ball
  · -- The center stays in the first shrunken ball.
    simpa [C, ε, Metric.mem_ball] using hε
  · -- Open metric balls are convex in these Euclidean coordinate spaces.
    simpa [C] using convex_ball u ε
  · -- The second shrunken ball is open for the same reason.
    simpa [D] using isOpen_ball
  · -- Its center also lies in the ball.
    simpa [D, ε, Metric.mem_ball] using hε
  · -- The second ball is convex as well.
    simpa [D] using convex_ball v ε
  · intro x hx y hy
    -- Route correction: the finite rectangle must now be produced directly from the slice balls,
    -- not via the stalled interior-domain lemma.
    let xRef : Fin m → ℝ := 2 • u - x
    let yRef : Fin n → ℝ := 2 • v - y
    have hxRef_mem : xRef ∈ C := by
      -- Reflection across `u` stays inside the symmetric first ball.
      simpa [C, xRef] using
        helperForTheorem_35_8_reflection_mem_ball (c := u) (x := x) (ε := ε) hx
    have hyRef_mem : yRef ∈ D := by
      -- The same symmetry holds in the second coordinate ball.
      simpa [D, yRef] using
        helperForTheorem_35_8_reflection_mem_ball (c := v) (x := y) (ε := ε) hy
    have hxFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal) :=
      hFirstFinite x <| hBallC <| by
        have hxDist : dist x u < ε := by
          simpa [C, Metric.mem_ball] using hx
        have hxDistC0 : dist x u < εC := lt_of_lt_of_le hxDist (min_le_left _ _)
        simpa [Metric.mem_ball] using hxDistC0
    have hxRefFinite : K xRef v ≠ (⊤ : EReal) ∧ K xRef v ≠ (⊥ : EReal) :=
      hFirstFinite xRef <| hBallC <| by
        have hxRefDist : dist xRef u < ε := by
          simpa [C, Metric.mem_ball] using hxRef_mem
        have hxRefDistC0 : dist xRef u < εC := lt_of_lt_of_le hxRefDist (min_le_left _ _)
        simpa [Metric.mem_ball] using hxRefDistC0
    have hyFinite : K u y ≠ (⊤ : EReal) ∧ K u y ≠ (⊥ : EReal) :=
      hSecondFinite y <| hBallD <| by
        have hyDist : dist y v < ε := by
          simpa [D, Metric.mem_ball] using hy
        have hyDistD0 : dist y v < εD := lt_of_lt_of_le hyDist (min_le_right _ _)
        simpa [Metric.mem_ball] using hyDistD0
    have hyRefFinite : K u yRef ≠ (⊤ : EReal) ∧ K u yRef ≠ (⊥ : EReal) :=
      hSecondFinite yRef <| hBallD <| by
        have hyRefDist : dist yRef v < ε := by
          simpa [D, Metric.mem_ball] using hyRef_mem
        have hyRefDistD0 : dist yRef v < εD := lt_of_lt_of_le hyRefDist (min_le_right _ _)
        simpa [Metric.mem_ball] using hyRefDistD0
    -- Once the reflected axis points are known to be finite, the remaining mixed-corner claim is
    -- exactly the delegated checkerboard-exclusion input.
    exact hCornerFinite hxFinite hxRefFinite hyFinite hyRefFinite



end Section35
end Chap07
